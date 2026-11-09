// gpu-timeshare: one GPU, many models, the OpenAI API in front.
//
//	gpu-timeshare serve  [--config FILE]               run the server
//	gpu-timeshare token  add NAME [--admin] | list | remove NAME
//	gpu-timeshare cache  stats | clear [--model NAME]
//	gpu-timeshare check  [--config FILE]               read the config and say what it holds
//	gpu-timeshare cert   --hosts a,b [--cert F] [--key F]   a self-signed certificate
//
// The config file is --config, or $TIMESHARE_CONFIG, or ./timeshare.toml.
package main

import (
	"context"
	"database/sql"
	"errors"
	"flag"
	"fmt"
	"log"
	"net"
	"net/http"
	"os"
	"os/signal"
	"strings"
	"syscall"
	"text/tabwriter"
	"time"

	"gpu-timeshare/internal/api"
	"gpu-timeshare/internal/auth"
	"gpu-timeshare/internal/batch"
	"gpu-timeshare/internal/config"
	"gpu-timeshare/internal/db"
	"gpu-timeshare/internal/queue"
	"gpu-timeshare/internal/sched"
	"gpu-timeshare/internal/tlsutil"
	"gpu-timeshare/internal/upstream"
)

const usage = `usage:
  gpu-timeshare serve  [--config FILE]
  gpu-timeshare token  add NAME [--admin] | list | remove NAME   [--config FILE]
  gpu-timeshare cache  stats | clear [--model NAME]              [--config FILE]
  gpu-timeshare check  [--config FILE]
  gpu-timeshare cert   --hosts NAME[,NAME,IP...] [--cert FILE] [--key FILE] [--days N] [--if-missing]
`

func main() {
	log.SetFlags(0)
	log.SetPrefix("gpu-timeshare: ")
	if len(os.Args) < 2 {
		fmt.Fprint(os.Stderr, usage)
		os.Exit(2)
	}
	var err error
	switch cmd, args := os.Args[1], os.Args[2:]; cmd {
	case "serve":
		err = serve(args)
	case "token":
		err = token(args)
	case "cache":
		err = cache(args)
	case "check":
		err = check(args)
	case "cert":
		err = tlsutil.CertCmd(args)
	case "-h", "--help", "help":
		fmt.Print(usage)
	default:
		fmt.Fprint(os.Stderr, usage)
		os.Exit(2)
	}
	if err != nil {
		log.Fatal(err)
	}
}

func configFlag(fs *flag.FlagSet) *string {
	def := os.Getenv("TIMESHARE_CONFIG")
	if def == "" {
		def = "timeshare.toml"
	}
	return fs.String("config", def, "the config file ($TIMESHARE_CONFIG)")
}

// parse lets flags come after positional arguments too.
func parse(fs *flag.FlagSet, args []string) []string {
	var pos []string
	for {
		fs.Parse(args)
		args = fs.Args()
		if len(args) == 0 {
			return pos
		}
		pos = append(pos, args[0])
		args = args[1:]
	}
}

func open(path string) (*config.Config, *sql.DB, error) {
	cfg, err := config.Load(path)
	if err != nil {
		return nil, nil, err
	}
	if err := cfg.EnsureDirs(); err != nil {
		return nil, nil, err
	}
	d, err := db.Open(cfg.DBPath())
	return cfg, d, err
}

func serve(args []string) error {
	fs := flag.NewFlagSet("serve", flag.ExitOnError)
	cfgPath := configFlag(fs)
	parse(fs, args)
	cfg, d, err := open(*cfgPath)
	if err != nil {
		return err
	}
	defer d.Close()

	q := &queue.Queue{DB: d, FilesDir: cfg.FilesDir()}
	if n, err := q.ForgetSingles(); err != nil {
		return err
	} else if n > 0 {
		log.Printf("dropped %d single request(s) whose callers left with the last run", n)
	}
	if err := upstream.StopUnits(cfg); err != nil {
		log.Printf("stopping the model units left from before: %v", err)
	}
	handler, sc := wire(cfg, d, q, log.Printf)
	srv := &http.Server{
		Handler:           handler,
		ReadHeaderTimeout: 30 * time.Second,
	}

	ln, err := net.Listen("tcp", cfg.Listen)
	if err != nil {
		return err
	}
	scheme := "http"
	if cfg.TLS.Cert != "" {
		certs, err := tlsutil.NewReloader(cfg.TLS.Cert, cfg.TLS.Key, log.Printf)
		if err != nil {
			return err
		}
		srv.TLSConfig, scheme = certs.Config(), "https"
	} else if host, _, _ := net.SplitHostPort(cfg.Listen); !loopback(host) {
		log.Printf("warning: listening on %s without TLS: tokens and requests cross the network in the clear", cfg.Listen)
	}

	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGINT, syscall.SIGTERM)
	defer stop()
	done := make(chan error, 1)
	go func() { done <- sc.Run(ctx) }()
	go func() {
		<-ctx.Done()
		sctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		srv.Shutdown(sctx)
	}()
	log.Printf("serving %d model(s) on %s://%s (state in %s)", len(cfg.Models), scheme, ln.Addr(), cfg.StateDir)
	if scheme == "https" {
		err = srv.ServeTLS(ln, "", "")
	} else {
		err = srv.Serve(ln)
	}
	if !errors.Is(err, http.ErrServerClosed) {
		stop()
		<-done
		return err
	}
	log.Printf("stopping the models")
	return <-done
}

func loopback(host string) bool {
	if host == "localhost" {
		return true
	}
	ip := net.ParseIP(host)
	return ip != nil && ip.IsLoopback()
}

func token(args []string) error {
	fs := flag.NewFlagSet("token", flag.ExitOnError)
	cfgPath := configFlag(fs)
	admin := fs.Bool("admin", false, "the client sees every client's files and batches")
	pos := parse(fs, args)
	if len(pos) == 0 {
		return errors.New("usage: gpu-timeshare token add NAME [--admin] | list | remove NAME")
	}
	_, d, err := open(*cfgPath)
	if err != nil {
		return err
	}
	defer d.Close()
	a := auth.New(d)
	switch {
	case pos[0] == "add" && len(pos) == 2:
		t, err := a.Add(pos[1], *admin)
		if err != nil {
			return err
		}
		fmt.Println(t)
		fmt.Fprintf(os.Stderr, "gpu-timeshare: client %s made; the token above is shown only now\n", pos[1])
	case pos[0] == "remove" && len(pos) == 2:
		return a.Remove(pos[1])
	case pos[0] == "list" && len(pos) == 1:
		cs, err := a.List()
		if err != nil {
			return err
		}
		w := tabwriter.NewWriter(os.Stdout, 0, 4, 2, ' ', 0)
		fmt.Fprintln(w, "NAME\tADMIN\tCREATED")
		for _, c := range cs {
			fmt.Fprintf(w, "%s\t%v\t%s\n", c.Name, c.Admin, c.Created.Format(time.RFC3339))
		}
		w.Flush()
	default:
		return errors.New("usage: gpu-timeshare token add NAME [--admin] | list | remove NAME")
	}
	return nil
}

func cache(args []string) error {
	fs := flag.NewFlagSet("cache", flag.ExitOnError)
	cfgPath := configFlag(fs)
	model := fs.String("model", "", "only this model's answers")
	pos := parse(fs, args)
	_, d, err := open(*cfgPath)
	if err != nil {
		return err
	}
	defer d.Close()
	q := &queue.Queue{DB: d}
	switch {
	case len(pos) == 1 && pos[0] == "stats":
		st, err := q.Stats()
		if err != nil {
			return err
		}
		w := tabwriter.NewWriter(os.Stdout, 0, 4, 2, ' ', 0)
		fmt.Fprintln(w, "MODEL\tIDENTITY\tANSWERS\tBYTES\tHITS\tMEAN")
		for _, s := range st {
			if *model != "" && s.Model != *model {
				continue
			}
			fmt.Fprintf(w, "%s\t%s\t%d\t%d\t%d\t%s\n", s.Model, s.Identity, s.Answers, s.Bytes, s.Hits,
				(time.Duration(s.MeanMs) * time.Millisecond).Round(time.Millisecond))
		}
		w.Flush()
	case len(pos) == 1 && pos[0] == "clear":
		n, err := q.Clear(*model)
		if err != nil {
			return err
		}
		fmt.Fprintf(os.Stderr, "gpu-timeshare: %d answer(s) dropped\n", n)
	default:
		return errors.New("usage: gpu-timeshare cache stats | clear [--model NAME]")
	}
	return nil
}

func check(args []string) error {
	fs := flag.NewFlagSet("check", flag.ExitOnError)
	cfgPath := configFlag(fs)
	parse(fs, args)
	cfg, err := config.Load(*cfgPath)
	if err != nil {
		return err
	}
	w := tabwriter.NewWriter(os.Stdout, 0, 4, 2, ' ', 0)
	fmt.Fprintf(w, "listen\t%s\n", cfg.Listen)
	fmt.Fprintf(w, "state\t%s\n", cfg.StateDir)
	fmt.Fprintln(w, "MODEL\tCONCURRENCY\tRUN\tCACHE\tIDENTITY")
	for _, n := range cfg.Names() {
		m := cfg.Models[n]
		how := "unit " + m.Unit
		if len(m.Command) > 0 {
			how = "command " + strings.Join(m.Command, " ")
			if len(how) > 60 {
				how = how[:57] + "..."
			}
		}
		fmt.Fprintf(w, "%s\t%d\t%s\t%v\t%s\n", n, m.Concurrency, how, m.Caches(cfg), m.Identity())
	}
	return w.Flush()
}

// wire builds the API and the scheduler over one database.
func wire(cfg *config.Config, d *sql.DB, q *queue.Queue, logf func(string, ...any)) (*api.Server, *sched.Scheduler) {
	bs := &batch.Store{DB: d, Cfg: cfg, Q: q}
	sc := &sched.Scheduler{Cfg: cfg, Q: q, B: bs, Logf: logf,
		NewServer: func(m *config.Model) (upstream.Server, error) { return upstream.New(cfg, m, logf) }}
	return &api.Server{Cfg: cfg, Auth: auth.New(d), Q: q, B: bs, Sched: sc, Logf: logf}, sc
}
