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
	key := func(r queue.Request) string { return r.Key }
	got, last := RoundRobin(by, key, nil, Owner{}, "", 5)
	if names(got) != "alice:a1 bob:b1 carol:c1 alice:a2 carol:c2" || last != "carol" {
		t.Errorf("got %s (last %s)", names(got), last)
	}
	// the next round starts after the last client served
	got, _ = RoundRobin(by, key, nil, Owner{}, "alice", 2)
	if names(got) != "bob:b1 carol:c1" {
		t.Errorf("after alice: %s", names(got))
	}
	// one question asked by two clients is picked once
	got, _ = RoundRobin(map[string][]queue.Request{"alice": reqs("alice", "k"), "bob": reqs("bob", "k", "b2")}, key, nil, Owner{}, "", 4)
	if names(got) != "alice:k bob:b2" {
		t.Errorf("shared key: %s", names(got))
	}
}

// the free slots go to whoever has the fewest requests in flight: alice
// holds three of the four slots, so the next two are bob's
func TestRoundRobinEvensTheSlots(t *testing.T) {
	by := map[string][]queue.Request{
		"alice": reqs("alice", "a1", "a2", "a3"),
		"bob":   reqs("bob", "b1", "b2", "b3"),
	}
	key := func(r queue.Request) string { return r.Key }
	got, _ := RoundRobin(by, key, map[string]int{"alice": 3, "bob": 0}, Owner{}, "bob", 2)
	if names(got) != "bob:b1 bob:b2" {
		t.Errorf("got %s", names(got))
	}
	// level again: they alternate
	got, _ = RoundRobin(by, key, map[string]int{"alice": 2, "bob": 2}, Owner{}, "alice", 3)
	if names(got) != "bob:b1 alice:a1 bob:b2" {
		t.Errorf("level: %s", names(got))
	}
}

// The tenant whose turn it is keeps half the card's slots while it has
// requests to give, whoever else has requests for the model: alice owns a
// card of four slots and holds none of them, so the first two free slots
// are hers, and the rest are shared as ever.
func TestRoundRobinOwnersHalf(t *testing.T) {
	by := map[string][]queue.Request{
		"alice": reqs("alice", "a1", "a2", "a3"),
		"bob":   reqs("bob", "b1", "b2", "b3"),
		"carol": reqs("carol", "c1"),
	}
	key := func(r queue.Request) string { return r.Key }
	got, _ := RoundRobin(by, key, nil, Owner{Tenant: "alice", Slots: 4}, "alice", 4)
	if names(got) != "alice:a1 alice:a2 bob:b1 carol:c1" {
		t.Errorf("got %s", names(got))
	}
	// she holds her half already: no exception
	got, _ = RoundRobin(by, key, map[string]int{"alice": 2}, Owner{Tenant: "alice", Held: 2, Slots: 4}, "alice", 2)
	if names(got) != "bob:b1 carol:c1" {
		t.Errorf("at her half: %s", names(got))
	}
	// one slot: it is the owner's
	got, _ = RoundRobin(by, key, nil, Owner{Tenant: "bob", Slots: 1}, "", 1)
	if names(got) != "bob:b1" {
		t.Errorf("one slot: %s", names(got))
	}
}
