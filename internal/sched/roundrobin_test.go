package sched

import (
	"fmt"
	"strings"
	"testing"

	"gpu-timeshare/internal/queue"
)

func reqs(client string, keys ...string) []queue.Request {
	var out []queue.Request
	for _, k := range keys {
		out = append(out, queue.Request{Client: client, Key: k})
	}
	return out
}

func names(rs []queue.Request) string {
	var s []string
	for _, r := range rs {
		s = append(s, fmt.Sprintf("%s:%s", r.Client, r.Key))
	}
	return strings.Join(s, " ")
}

func TestRoundRobin(t *testing.T) {
	by := map[string][]queue.Request{
		"alice": reqs("alice", "a1", "a2", "a3", "a4"),
		"bob":   reqs("bob", "b1"),
		"carol": reqs("carol", "c1", "c2"),
	}
	got, last := RoundRobin(by, "", 5)
	if names(got) != "alice:a1 bob:b1 carol:c1 alice:a2 carol:c2" || last != "carol" {
		t.Errorf("got %s (last %s)", names(got), last)
	}
	// the next round starts after the last client served
	got, _ = RoundRobin(by, "alice", 2)
	if names(got) != "bob:b1 carol:c1" {
		t.Errorf("after alice: %s", names(got))
	}
	// one question asked by two clients is picked once
	got, _ = RoundRobin(map[string][]queue.Request{"alice": reqs("alice", "k"), "bob": reqs("bob", "k", "b2")}, "", 4)
	if names(got) != "alice:k bob:b2" {
		t.Errorf("shared key: %s", names(got))
	}
}
