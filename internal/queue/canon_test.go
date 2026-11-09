package queue

import (
	"bytes"
	"testing"
)

var canonSeeds = []string{
	`{"b":1,"a":[1,2,{"z":null,"y":true}],"c":"x"}`,
	`{"a":1,"a":2}`, `{"a":{"x":1},"b":0,"a":{"y":2}}`,
	` { "model" : "m" , "messages" : [ ] , "t" : -0.5e+10 } `,
	`{"s":"café \"q\" \/ <>&","ka":1,"ka":2}`, `{"s":"café "}`,
	`{"a":1}]`, `{"a":1} x`, `{"a":01}`, `{"a":1.}`, `[1,2,]`, `{"a":"\x01"}`,
	`"top"`, `12`, `null`, `[]`, `{}`, `{"":1,"\u0000":2}`, `{"n":1E5,"m":-0}`,
	"{\"bad\":\"\xff\"}", `{"a":tru}`, ``, `   `,
}

// FuzzCanonical: the fast path must agree with encoding/json byte for byte,
// or every cache key would change.
func FuzzCanonical(f *testing.F) {
	for _, s := range canonSeeds {
		f.Add([]byte(s))
	}
	f.Fuzz(func(t *testing.T, in []byte) {
		fast, ferr := fastCanonical(in)
		if ferr != nil {
			return // the slow path's answer is the answer
		}
		slow, serr := slowCanonical(in)
		if serr != nil {
			t.Fatalf("fast path accepted %q, encoding/json refuses: %v", in, serr)
		}
		if !bytes.Equal(fast, slow) {
			t.Fatalf("%q: fast %q, slow %q", in, fast, slow)
		}
	})
}

func TestMembers(t *testing.T) {
	m, err := Members([]byte(` {"custom_id":"x","body":{"model":"a","k":[1,{"q":"}"}]},"method":"POST","custom_id":"y"} `))
	if err != nil {
		t.Fatal(err)
	}
	if got := string(m["body"]); got != `{"model":"a","k":[1,{"q":"}"}]}` {
		t.Errorf("body %s", got)
	}
	if s, _ := String(m["custom_id"]); s != "y" {
		t.Errorf("custom_id %q, want the last", s)
	}
	if s, _ := String(m["method"]); s != "POST" {
		t.Errorf("method %q", s)
	}
	for _, bad := range []string{`{"a":1`, `[1]`, `{"a":1}x`, `{"a":tru}`} {
		if _, err := Members([]byte(bad)); err == nil {
			t.Errorf("%s: no error", bad)
		}
	}
}

// a non-ASCII prompt keeps the picture beside it on the fast path
func TestCanonicalMixed(t *testing.T) {
	in := []byte(`{"z":"` + string(bytes.Repeat([]byte("QUJD"), 1000)) + `","t":"説明して é \/","ké":1,"ké":2,"a":"<&>"}`)
	fast, err := fastCanonical(in)
	if err != nil {
		t.Fatalf("fast path refused it: %v", err)
	}
	slow, _ := slowCanonical(in)
	if !bytes.Equal(fast, slow) {
		t.Fatalf("fast %.80q\nslow %.80q", fast, slow)
	}
}
