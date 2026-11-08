// Package upstream starts, asks and stops the model servers.
//
// The contract a model server keeps is the OpenAI HTTP API: it answers
// GET <ready> (by default /v1/models) with 200 once it can take requests,
// and serves the endpoints the config lists. Nothing else about it is
// gpu-timeshare's business. Two ways to run one:
//
//   - Process: a command gpu-timeshare runs itself, in its own process
//     group, so stopping it takes every child with it (vllm's workers are
//     what hold the VRAM).
//   - Unit: a systemd unit, started and stopped with systemctl. systemd
//     owns it from there: its cgroup (stopping kills every process in it),
//     its sandbox, its logs. gpu-timeshare never chooses what runs.
package upstream

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"gpu-timeshare/internal/config"
)

// Server is one model's server.
type Server interface {
	// Start returns once the server answers its ready check.
	Start(ctx context.Context) error
	// Do forwards one request (an endpoint path and a JSON body whose
	// "model" is already the upstream's name) and returns its reply.
	Do(ctx context.Context, endpoint string, body []byte) (status int, reply []byte, err error)
	// UpstreamModel is the name the server expects in "model".
	UpstreamModel() string
	Stop() error
	Alive() bool
}

// New makes the Server a model's config describes.
func New(cfg *config.Config, m *config.Model, logf func(string, ...any)) (Server, error) {
	c := &client{model: m, timeout: cfg.Scheduler.RequestTimeout.Duration, logf: logf}
	if m.Unit != "" {
		c.setURL(m.URL)
		return &Unit{client: c, systemctl: cfg.Systemctl, unit: m.Unit}, nil
	}
	return &Process{client: c, cfg: cfg}, nil
}

// ---- talking to it ---------------------------------------------------------

type client struct {
	model    *config.Model
	timeout  time.Duration
	logf     func(string, ...any)
	base     string // http://host:port, or http://upstream for a socket
	http     *http.Client
	upstream string
}

func (c *client) setURL(u string) {
	tr := http.DefaultTransport.(*http.Transport).Clone()
	tr.MaxIdleConnsPerHost = 64
	if path, ok := strings.CutPrefix(u, "unix:"); ok {
		tr.DialContext = func(ctx context.Context, _, _ string) (net.Conn, error) {
			var d net.Dialer
			return d.DialContext(ctx, "unix", path)
		}
		c.base = "http://upstream"
	} else {
		c.base = strings.TrimRight(u, "/")
	}
	c.http = &http.Client{Transport: tr}
}

func (c *client) UpstreamModel() string { return c.upstream }

// ready is one poll of the ready check. When it is /v1/models and no
// upstream_model is set, the first model listed becomes the name.
func (c *client) ready(ctx context.Context) bool {
	ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
	defer cancel()
	req, _ := http.NewRequestWithContext(ctx, "GET", c.base+c.model.Ready, nil)
	resp, err := c.http.Do(req)
	if err != nil {
		return false
	}
	defer resp.Body.Close()
	body, _ := io.ReadAll(io.LimitReader(resp.Body, 1<<20))
	if resp.StatusCode != 200 {
		return false
	}
	if c.model.UpstreamModel != "" {
		c.upstream = c.model.UpstreamModel
		return true
	}
	name, err := c.firstModel(ctx, body)
	if err != nil {
		c.logf("%s: up, but %v", c.model.Name, err)
		return false
	}
	c.upstream = name
	return true
}

func (c *client) firstModel(ctx context.Context, body []byte) (string, error) {
	if c.model.Ready != "/v1/models" {
		req, _ := http.NewRequestWithContext(ctx, "GET", c.base+"/v1/models", nil)
		resp, err := c.http.Do(req)
		if err != nil {
			return "", err
		}
		defer resp.Body.Close()
		body, _ = io.ReadAll(io.LimitReader(resp.Body, 1<<20))
	}
	var list struct {
		Data []struct {
			ID string `json:"id"`
		} `json:"data"`
	}
	if err := json.Unmarshal(body, &list); err != nil || len(list.Data) == 0 || list.Data[0].ID == "" {
		return "", errors.New("/v1/models names no model (set upstream_model)")
	}
	return list.Data[0].ID, nil
}

func (c *client) Do(ctx context.Context, endpoint string, body []byte) (int, []byte, error) {
	if c.timeout > 0 {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, c.timeout)
		defer cancel()
	}
	req, err := http.NewRequestWithContext(ctx, "POST", c.base+endpoint, bytes.NewReader(body))
	if err != nil {
		return 0, nil, err
	}
	req.Header.Set("content-type", "application/json")
	resp, err := c.http.Do(req)
	if err != nil {
		return 0, nil, err
	}
	defer resp.Body.Close()
	out, err := io.ReadAll(resp.Body)
	if err != nil {
		return 0, nil, err
	}
	return resp.StatusCode, out, nil
}

// waitReady polls until ready, the deadline, or alive() says it is gone.
func (c *client) waitReady(ctx context.Context, alive func() error) error {
	ctx, cancel := context.WithTimeout(ctx, c.model.StartTimeout.Duration)
	defer cancel()
	tick := time.NewTicker(500 * time.Millisecond)
	defer tick.Stop()
	for {
		if c.ready(ctx) {
			return nil
		}
		if err := alive(); err != nil {
			return err
		}
		select {
		case <-ctx.Done():
			return fmt.Errorf("not ready after %s", c.model.StartTimeout.Duration)
		case <-tick.C:
		}
	}
}

// ---- a child process -------------------------------------------------------

type Process struct {
	*client
	cfg *config.Config

	cmd     *exec.Cmd
	exited  chan struct{}
	waitErr error
}

// freePort asks the kernel for a port nobody holds. It can be taken again
// before the server binds it; the start then fails and is retried.
func freePort() (int, error) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		return 0, err
	}
	defer l.Close()
	return l.Addr().(*net.TCPAddr).Port, nil
}

// Expand fills {port} and {socket} into a command and its URL.
func Expand(cfg *config.Config, m *config.Model) (argv []string, url string, err error) {
	joined := strings.Join(m.Command, "\x00") + m.URL
	port, socket := "", filepath.Join(cfg.SocketDir(), sanitize(m.Name)+".sock")
	if strings.Contains(joined, "{port}") {
		p, err := freePort()
		if err != nil {
			return nil, "", err
		}
		port = strconv.Itoa(p)
	}
	r := strings.NewReplacer("{port}", port, "{socket}", socket)
	for _, a := range m.Command {
		argv = append(argv, r.Replace(a))
	}
	url = r.Replace(m.URL)
	if url == "" {
		if strings.Contains(strings.Join(m.Command, " "), "{socket}") {
			url = "unix:" + socket
		} else {
			url = "http://127.0.0.1:" + port
		}
	}
	return argv, url, nil
}

func sanitize(name string) string {
	return strings.NewReplacer("/", "_", ":", "_").Replace(name)
}

func (p *Process) Start(ctx context.Context) error {
	argv, url, err := Expand(p.cfg, p.model)
	if err != nil {
		return err
	}
	p.setURL(url)
	if path, ok := strings.CutPrefix(url, "unix:"); ok {
		os.Remove(path) // a stale socket from a server that died
	}
	log, err := os.OpenFile(filepath.Join(p.cfg.LogsDir(), sanitize(p.model.Name)+".log"),
		os.O_WRONLY|os.O_CREATE|os.O_APPEND, 0o640)
	if err != nil {
		return err
	}
	fmt.Fprintf(log, "\n--- %s gpu-timeshare: starting %q\n", time.Now().Format(time.RFC3339), argv)
	p.cmd = exec.Command(argv[0], argv[1:]...)
	p.cmd.Env = os.Environ()
	for k, v := range p.model.Environment {
		p.cmd.Env = append(p.cmd.Env, k+"="+v)
	}
	p.cmd.Stdout, p.cmd.Stderr = log, log
	p.cmd.SysProcAttr = &syscall.SysProcAttr{Setpgid: true, Pdeathsig: syscall.SIGKILL}
	if err := p.cmd.Start(); err != nil {
		log.Close()
		return err
	}
	p.exited = make(chan struct{})
	go func() { p.waitErr = p.cmd.Wait(); log.Close(); close(p.exited) }()
	err = p.waitReady(ctx, func() error {
		if !p.Alive() {
			return fmt.Errorf("exited while starting (%v); see %s", p.waitErr, log.Name())
		}
		return nil
	})
	if err != nil {
		p.Stop()
	}
	return err
}

func (p *Process) Alive() bool {
	if p.exited == nil {
		return false
	}
	select {
	case <-p.exited:
		return false
	default:
		return true
	}
}

func (p *Process) signal(sig syscall.Signal) {
	if p.cmd != nil && p.cmd.Process != nil {
		syscall.Kill(-p.cmd.Process.Pid, sig) // the group: its workers too
	}
}

// Stop: SIGTERM to the group, SIGKILL after the grace period, and SIGKILL
// again for any worker the leader left behind (it would hold VRAM).
func (p *Process) Stop() error {
	if p.exited == nil {
		return nil
	}
	if p.Alive() {
		p.signal(syscall.SIGTERM)
		select {
		case <-p.exited:
		case <-time.After(p.cfg.Scheduler.StopGrace.Duration):
			p.signal(syscall.SIGKILL)
			<-p.exited
		}
	}
	p.signal(syscall.SIGKILL)
	return nil
}

// ---- a systemd unit --------------------------------------------------------

type Unit struct {
	*client
	systemctl []string
	unit      string

	mu      sync.Mutex
	checked time.Time
	active  bool
}

func (u *Unit) ctl(ctx context.Context, args ...string) (string, error) {
	argv := append(append([]string(nil), u.systemctl...), args...)
	cmd := exec.CommandContext(ctx, argv[0], argv[1:]...)
	out, err := cmd.CombinedOutput()
	if err != nil {
		return string(out), fmt.Errorf("%s: %v: %s", strings.Join(argv, " "), err, strings.TrimSpace(string(out)))
	}
	return strings.TrimSpace(string(out)), nil
}

// state is the unit's ActiveState: active, activating, failed, inactive...
func (u *Unit) state(ctx context.Context) string {
	out, err := u.ctl(ctx, "show", "--property=ActiveState", "--value", u.unit)
	if err != nil {
		return "unknown"
	}
	return out
}

func (u *Unit) Start(ctx context.Context) error {
	// a unit left failed by its last run would refuse to start
	u.ctl(ctx, "reset-failed", u.unit)
	if _, err := u.ctl(ctx, "start", "--no-block", u.unit); err != nil {
		return err
	}
	u.mu.Lock()
	u.active, u.checked = true, time.Now()
	u.mu.Unlock()
	err := u.waitReady(ctx, func() error {
		switch s := u.state(ctx); s {
		case "active", "activating", "reloading":
			return nil
		default:
			return fmt.Errorf("unit %s is %s while starting; see journalctl -u %s", u.unit, s, u.unit)
		}
	})
	if err != nil {
		u.Stop()
	}
	return err
}

// Stop hands it to systemd: SIGTERM, then SIGKILL to the whole cgroup
// after the unit's TimeoutStopSec. It returns once the unit is down.
func (u *Unit) Stop() error {
	u.mu.Lock()
	u.active = false
	u.mu.Unlock()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
	defer cancel()
	_, err := u.ctl(ctx, "stop", u.unit)
	return err
}

// Alive asks systemd, at most every two seconds.
func (u *Unit) Alive() bool {
	u.mu.Lock()
	defer u.mu.Unlock()
	if !u.active {
		return false
	}
	if time.Since(u.checked) < 2*time.Second {
		return true
	}
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	s := u.state(ctx)
	u.checked = time.Now()
	if s == "unknown" {
		return true // systemctl itself failed; don't kill a model for that
	}
	u.active = s == "active" || s == "activating" || s == "reloading"
	return u.active
}

// StopUnits stops every unit-run model: on start-up, so a unit left
// running by a gpu-timeshare that crashed isn't holding the card unseen.
func StopUnits(cfg *config.Config) error {
	var errs []error
	for _, n := range cfg.Names() {
		u := cfg.Models[n].Unit
		if u == "" {
			continue
		}
		// one call per unit: polkit refused one "systemctl stop a b" while
		// allowing each alone (the VM test), so a rule naming exactly these
		// units is enough
		argv := append(append([]string(nil), cfg.Systemctl...), "stop", u)
		if out, err := exec.Command(argv[0], argv[1:]...).CombinedOutput(); err != nil {
			errs = append(errs, fmt.Errorf("%s: %v: %s", strings.Join(argv, " "), err, strings.TrimSpace(string(out))))
		}
	}
	return errors.Join(errs...)
}
