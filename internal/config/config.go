// Package config reads gpu-timeshare's TOML configuration: where it
// listens, how the card is shared, and the model servers it may start.
//
// A model is a server that speaks the OpenAI HTTP API. gpu-timeshare
// starts it (a command it runs itself, or a systemd unit it starts and
// stops), waits until it answers, forwards requests to it, and stops it
// to make room for another.
package config

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"

	"github.com/BurntSushi/toml"
)

// Duration is a Go duration ("90s", "10m", "2h") or a number of days ("30d").
// "0" means "never" wherever a duration bounds something.
type Duration struct{ time.Duration }

func (d *Duration) UnmarshalText(b []byte) error {
	s := strings.TrimSpace(string(b))
	if n, ok := strings.CutSuffix(s, "d"); ok {
		days, err := strconv.ParseFloat(n, 64)
		if err != nil {
			return fmt.Errorf("duration %q: %v", s, err)
		}
		d.Duration = time.Duration(days * 24 * float64(time.Hour))
		return nil
	}
	v, err := time.ParseDuration(s)
	if err != nil {
		return fmt.Errorf("duration %q: %v", s, err)
	}
	d.Duration = v
	return nil
}

// Size is a byte count: a number, or one with a unit (KiB, MiB, GiB, TiB;
// KB, MB, GB, TB). "0" means "unlimited" wherever a size bounds something.
type Size int64

func (z *Size) UnmarshalText(b []byte) error {
	s := strings.TrimSpace(string(b))
	units := []struct {
		suffix string
		mult   int64
	}{{"KiB", 1 << 10}, {"MiB", 1 << 20}, {"GiB", 1 << 30}, {"TiB", 1 << 40},
		{"KB", 1e3}, {"MB", 1e6}, {"GB", 1e9}, {"TB", 1e12}, {"B", 1}}
	mult := int64(1)
	for _, u := range units {
		if n, ok := strings.CutSuffix(s, u.suffix); ok {
			s, mult = strings.TrimSpace(n), u.mult
			break
		}
	}
	v, err := strconv.ParseFloat(s, 64)
	if err != nil || v < 0 {
		return fmt.Errorf("size %q: want a number of bytes, optionally with KiB/MiB/GiB", string(b))
	}
	*z = Size(v * float64(mult))
	return nil
}

type Config struct {
	Listen   string `toml:"listen"`    // host:port
	StateDir string `toml:"state_dir"` // the database, files, logs, sockets
	// systemctl and its leading arguments, for models run as units
	// (["systemctl", "--user"] for a user manager)
	Systemctl []string `toml:"systemctl"`

	TLS       TLS               `toml:"tls"`
	Scheduler Scheduler         `toml:"scheduler"`
	Limits    Limits            `toml:"limits"`
	Cache     Cache             `toml:"cache"`
	Endpoints []string          `toml:"endpoints"` // the OpenAI endpoints requests may name
	Models    map[string]*Model `toml:"models"`

	Path string `toml:"-"` // the file it came from
}

type TLS struct {
	Cert string `toml:"cert"`
	Key  string `toml:"key"`
}

type Scheduler struct {
	Capacity       float64  `toml:"capacity"`        // what the loaded models' costs must fit in
	Idle           Duration `toml:"idle"`            // stop a model after this long with no work (0: never)
	MaxTimeslice   Duration `toml:"max_timeslice"`   // the models on the card give way after this, if another model waits
	MaxAttempts    int      `toml:"max_attempts"`    // per request, before it fails
	StartTimeout   Duration `toml:"start_timeout"`   // default for every model
	RequestTimeout Duration `toml:"request_timeout"` // one request to a model
	StopGrace      Duration `toml:"stop_grace"`      // SIGTERM to SIGKILL, for commands
	BrokenFor      Duration `toml:"broken_for"`      // after failing to start twice, refuse a model this long
}

type Limits struct {
	MaxBody       Size     `toml:"max_body"`        // one request
	MaxFile       Size     `toml:"max_file"`        // one uploaded file
	MaxBatchLines int      `toml:"max_batch_lines"` // requests in one batch
	MaxWindow     Duration `toml:"max_window"`      // the longest completion_window accepted
	FileRetention Duration `toml:"file_retention"`  // files older than this are deleted (0: kept)
}

type Cache struct {
	Enabled   bool     `toml:"enabled"`
	MaxAge    Duration `toml:"max_age"`    // drop answers older than this (0: never)
	MaxUnused Duration `toml:"max_unused"` // drop answers not served for this long (0: never)
	MaxSize   Size     `toml:"max_size"`   // drop the least recently used past this (0: unlimited)
}

type Model struct {
	// how it runs: exactly one of these
	Command []string `toml:"command"` // run as a child process; {port} and {socket} are filled in
	Unit    string   `toml:"unit"`    // a systemd unit, started and stopped with systemctl

	// where it answers: http://host:port or unix:/path. A command that
	// names {socket} or {port} gets its URL from that.
	URL string `toml:"url"`

	Cost          float64           `toml:"cost"`           // its share of capacity
	Concurrency   int               `toml:"concurrency"`    // requests in flight to it
	Ready         string            `toml:"ready"`          // GET path that answers 200 once it is up
	UpstreamModel string            `toml:"upstream_model"` // the name it expects (default: the first /v1/models lists)
	Fingerprint   string            `toml:"fingerprint"`    // what identifies its answers; part of the cache key
	StartTimeout  Duration          `toml:"start_timeout"`
	Cache         *bool             `toml:"cache"` // default: [cache].enabled
	Environment   map[string]string `toml:"environment"`

	Name string `toml:"-"`
}

// Caches says whether this model's answers are cached.
func (m *Model) Caches(c *Config) bool {
	if m.Cache != nil {
		return *m.Cache && c.Cache.Enabled
	}
	return c.Cache.Enabled
}

var validName = regexp.MustCompile(`^[A-Za-z0-9][A-Za-z0-9._:/-]{0,127}$`)

// Load reads and checks a config file, filling in the defaults.
func Load(path string) (*Config, error) {
	c := Default()
	md, err := toml.DecodeFile(path, c)
	if err != nil {
		return nil, err
	}
	if und := md.Undecoded(); len(und) > 0 {
		var keys []string
		for _, k := range und {
			keys = append(keys, k.String())
		}
		return nil, fmt.Errorf("%s: unknown setting(s): %s", path, strings.Join(keys, ", "))
	}
	c.Path = path
	if err := c.check(); err != nil {
		return nil, fmt.Errorf("%s: %w", path, err)
	}
	return c, nil
}

// Default is every setting's default; models come from the file.
func Default() *Config {
	return &Config{
		Listen:    "127.0.0.1:8100",
		StateDir:  ".",
		Systemctl: []string{"systemctl"},
		Scheduler: Scheduler{
			Capacity:       1.0,
			Idle:           Duration{10 * time.Minute},
			MaxTimeslice:   Duration{2 * time.Hour},
			MaxAttempts:    3,
			StartTimeout:   Duration{15 * time.Minute},
			RequestTimeout: Duration{10 * time.Minute},
			StopGrace:      Duration{30 * time.Second},
			BrokenFor:      Duration{5 * time.Minute},
		},
		Limits: Limits{
			MaxBody:       64 << 20,
			MaxFile:       1 << 30,
			MaxBatchLines: 50000,
			MaxWindow:     Duration{7 * 24 * time.Hour},
			FileRetention: Duration{30 * 24 * time.Hour},
		},
		Cache:     Cache{Enabled: true},
		Endpoints: []string{"/v1/chat/completions", "/v1/completions", "/v1/embeddings"},
	}
}

func (c *Config) check() error {
	if (c.TLS.Cert == "") != (c.TLS.Key == "") {
		return errors.New("tls: cert and key go together")
	}
	if c.Scheduler.Capacity <= 0 {
		return errors.New("scheduler.capacity must be positive")
	}
	if c.Scheduler.MaxAttempts < 1 {
		return errors.New("scheduler.max_attempts must be at least 1")
	}
	if len(c.Systemctl) == 0 {
		return errors.New("systemctl must name a command")
	}
	for _, e := range c.Endpoints {
		if !strings.HasPrefix(e, "/v1/") {
			return fmt.Errorf("endpoint %q: want a path under /v1/", e)
		}
	}
	if len(c.Models) == 0 {
		return errors.New("no [models.NAME] sections")
	}
	for name, m := range c.Models {
		m.Name = name
		if !validName.MatchString(name) {
			return fmt.Errorf("model %q: a name is letters, digits and . _ : / - (at most 128)", name)
		}
		if (len(m.Command) == 0) == (m.Unit == "") {
			return fmt.Errorf("model %s: give exactly one of command or unit", name)
		}
		if m.Unit != "" && m.URL == "" {
			return fmt.Errorf("model %s: a unit needs a url", name)
		}
		if len(m.Command) > 0 && m.URL == "" {
			joined := strings.Join(m.Command, " ")
			if !strings.Contains(joined, "{socket}") && !strings.Contains(joined, "{port}") {
				return fmt.Errorf("model %s: the command names neither {socket} nor {port}, so give a url", name)
			}
		}
		if m.URL != "" && !strings.HasPrefix(m.URL, "http://") && !strings.HasPrefix(m.URL, "https://") &&
			!strings.HasPrefix(m.URL, "unix:") {
			return fmt.Errorf("model %s: url %q: want http://, https:// or unix:", name, m.URL)
		}
		if m.Cost < 0 || m.Cost > c.Scheduler.Capacity {
			return fmt.Errorf("model %s: cost %g does not fit in capacity %g", name, m.Cost, c.Scheduler.Capacity)
		}
		if m.Concurrency == 0 {
			m.Concurrency = 4
		}
		if m.Concurrency < 0 {
			return fmt.Errorf("model %s: concurrency must be positive", name)
		}
		if m.Ready == "" {
			m.Ready = "/v1/models"
		}
		if !strings.HasPrefix(m.Ready, "/") {
			return fmt.Errorf("model %s: ready %q: want a path", name, m.Ready)
		}
		if m.StartTimeout.Duration == 0 {
			m.StartTimeout = c.Scheduler.StartTimeout
		}
	}
	return nil
}

// Identity is what the cache key takes for a model: its fingerprint, or
// when none is set, how it is run (the command or the unit), which on nix
// names the weights' store path.
func (m *Model) Identity() string {
	if m.Fingerprint != "" {
		return m.Fingerprint
	}
	b, _ := json.Marshal(struct {
		Command []string `json:"command,omitempty"`
		Unit    string   `json:"unit,omitempty"`
		Model   string   `json:"upstream_model,omitempty"`
	}{m.Command, m.Unit, m.UpstreamModel})
	h := sha256.Sum256(b)
	return "run:" + hex.EncodeToString(h[:16])
}

// Names are the models, sorted.
func (c *Config) Names() []string {
	var out []string
	for n := range c.Models {
		out = append(out, n)
	}
	sort.Strings(out)
	return out
}

func (c *Config) DBPath() string    { return filepath.Join(c.StateDir, "timeshare.db") }
func (c *Config) FilesDir() string  { return filepath.Join(c.StateDir, "files") }
func (c *Config) LogsDir() string   { return filepath.Join(c.StateDir, "logs") }
func (c *Config) SocketDir() string { return filepath.Join(c.StateDir, "run") }
func (c *Config) EnsureDirs() error {
	for _, d := range []string{c.StateDir, c.FilesDir(), c.LogsDir(), c.SocketDir()} {
		if err := os.MkdirAll(d, 0o750); err != nil {
			return err
		}
	}
	return nil
}

func (c *Config) Allows(endpoint string) bool {
	for _, e := range c.Endpoints {
		if e == endpoint {
			return true
		}
	}
	return false
}
