package config

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func load(t *testing.T, s string) (*Config, error) {
	t.Helper()
	p := filepath.Join(t.TempDir(), "c.toml")
	os.WriteFile(p, []byte(s), 0o644)
	return Load(p)
}

func TestLoad(t *testing.T) {
	c, err := load(t, `
listen = "0.0.0.0:9000"
[scheduler]
idle = "0"
max_timeslice = "1.5h"
[limits]
max_file = "2GiB"
file_retention = "30d"
[cache]
max_size = "500 MB"
max_unused = "90d"
[models.qwen]
command = ["vllm", "serve", "/nix/store/x-qwen", "--uds", "{socket}"]
[models.pixai]
unit = "pixai.service"
url = "unix:/run/pixai.sock"
concurrency = 16
cache = false
fingerprint = "pixai-v1"
`)
	if err != nil {
		t.Fatal(err)
	}
	if c.Scheduler.Idle.Duration != 0 || c.Scheduler.MaxTimeslice.Duration != 90*time.Minute ||
		c.Limits.MaxFile != 2<<30 || c.Limits.FileRetention.Duration != 30*24*time.Hour ||
		c.Cache.MaxSize != 500e6 || c.Cache.MaxUnused.Duration != 90*24*time.Hour {
		t.Errorf("parsed: %+v %+v %+v", c.Scheduler, c.Limits, c.Cache)
	}
	q, p := c.Models["qwen"], c.Models["pixai"]
	if q.Concurrency != 4 || q.Ready != "/v1/models" || q.StartTimeout.Duration != 15*time.Minute || !q.Caches(c) {
		t.Errorf("qwen's defaults: %+v", q)
	}
	if p.Caches(c) || p.Identity() != "pixai-v1" {
		t.Errorf("pixai: caches %v identity %q", p.Caches(c), p.Identity())
	}
	if !strings.HasPrefix(q.Identity(), "run:") {
		t.Errorf("qwen's identity %q", q.Identity())
	}
	// the identity follows the command, which names the weights
	q2 := *q
	q2.Command = []string{"vllm", "serve", "/nix/store/y-qwen", "--uds", "{socket}"}
	if q2.Identity() == q.Identity() {
		t.Error("different weights, same identity")
	}
}

func TestLoadRefuses(t *testing.T) {
	for want, s := range map[string]string{
		"unknown setting":          "[models.a]\ncommand = [\"x\", \"{port}\"]\ncots = 1\n",
		"exactly one of":           "[models.a]\ncommand = [\"x\", \"{port}\"]\nunit = \"a.service\"\n",
		"a unit needs a url":       "[models.a]\nunit = \"a.service\"\n",
		"neither {socket} nor":     "[models.a]\ncommand = [\"x\"]\n",
		"models.a.cost":            "[models.a]\ncommand = [\"x\", \"{port}\"]\ncost = 0.5\n",
		"no [models.NAME]":         "listen = \"x:1\"\n",
		"cert and key go together": "[tls]\ncert = \"a\"\n[models.a]\ncommand = [\"x\", \"{port}\"]\n",
		"duration":                 "[scheduler]\nidle = \"soon\"\n[models.a]\ncommand = [\"x\", \"{port}\"]\n",
		"size":                     "[limits]\nmax_file = \"big\"\n[models.a]\ncommand = [\"x\", \"{port}\"]\n",
		"url":                      "[models.a]\nunit = \"a.service\"\nurl = \"ftp://x\"\n",
		"must name {gpu}":          "gpus = [\"0\", \"1\"]\n[models.a]\nunit = \"a.service\"\nurl = \"unix:/run/a.sock\"\n",
		"named twice":              "gpus = [\"0\", \"0\"]\n[models.a]\ncommand = [\"x\", \"{port}\"]\n",
		"load_ratio":               "[scheduler]\nload_ratio = -1\n[models.a]\ncommand = [\"x\", \"{port}\"]\n",
	} {
		_, err := load(t, s)
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("%q: %v, want %q", s, err, want)
		}
	}
}
