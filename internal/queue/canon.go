package queue

import (
	"bytes"
	"encoding/json"
	"errors"
	"slices"
)

// The fast path of Canonical and the scanner the batch reader uses. A
// request is mostly one long base64 string (a picture), and the slow path
// -- decode into an any, encode it again -- runs at ~85 MB/s on one, slower
// than a gigabit upload. Here a string the encoder would write back
// unchanged (printable ASCII, no escapes) is copied as it is.
//
// The output must be byte-identical to the slow path's, or every cache key
// changes: anything this code is not sure of (an escape, non-ASCII, deep
// nesting, anything malformed) returns errSlow and the caller asks
// encoding/json. FuzzCanonical holds the two together.

var errSlow = errors.New("not on the fast path")

const maxDepth = 512

type canon struct {
	in    []byte
	i     int
	out   []byte
	depth int
	tmp   []byte
}

func fastCanonical(body []byte) ([]byte, error) {
	c := canon{in: body, out: make([]byte, 0, len(body))}
	if err := c.value(); err != nil {
		return nil, err
	}
	c.ws()
	if c.i != len(c.in) {
		return nil, errSlow
	}
	return c.out, nil
}

func (c *canon) ws() {
	for c.i < len(c.in) {
		switch c.in[c.i] {
		case ' ', '\t', '\n', '\r':
			c.i++
		default:
			return
		}
	}
}

func (c *canon) value() error {
	c.ws()
	if c.i >= len(c.in) {
		return errSlow
	}
	switch b := c.in[c.i]; {
	case b == '{':
		return c.object()
	case b == '[':
		return c.array()
	case b == '"':
		_, err := c.str()
		return err
	case b == '-' || (b >= '0' && b <= '9'):
		e, ok := scanNumber(c.in, c.i)
		if !ok {
			return errSlow
		}
		c.out = append(c.out, c.in[c.i:e]...)
		c.i = e
		return nil
	default:
		for _, lit := range [...]string{"true", "false", "null"} {
			if bytes.HasPrefix(c.in[c.i:], []byte(lit)) {
				c.out = append(c.out, lit...)
				c.i += len(lit)
				return nil
			}
		}
		return errSlow
	}
}

func (c *canon) array() error {
	if c.depth++; c.depth > maxDepth {
		return errSlow
	}
	defer func() { c.depth-- }()
	c.i++
	c.out = append(c.out, '[')
	c.ws()
	if c.i < len(c.in) && c.in[c.i] == ']' {
		c.i++
		c.out = append(c.out, ']')
		return nil
	}
	for {
		if err := c.value(); err != nil {
			return err
		}
		c.ws()
		if c.i >= len(c.in) {
			return errSlow
		}
		switch c.in[c.i] {
		case ',':
			c.i++
			c.out = append(c.out, ',')
		case ']':
			c.i++
			c.out = append(c.out, ']')
			return nil
		default:
			return errSlow
		}
	}
}

type member struct {
	key        string // decoded: what the encoder sorts by
	start, end int    // the member's `"key":value` in c.out
}

// object writes its members in order, then puts them in key order -- Go's
// encoder sorts a map's keys -- keeping the last of duplicates, as decoding
// into a map does.
func (c *canon) object() error {
	if c.depth++; c.depth > maxDepth {
		return errSlow
	}
	defer func() { c.depth-- }()
	c.i++
	c.out = append(c.out, '{')
	base := len(c.out)
	var ms []member
	c.ws()
	if c.i < len(c.in) && c.in[c.i] == '}' {
		c.i++
		c.out = append(c.out, '}')
		return nil
	}
	for {
		c.ws()
		if c.i >= len(c.in) || c.in[c.i] != '"' {
			return errSlow
		}
		m := member{start: len(c.out)}
		var err error
		if m.key, err = c.str(); err != nil {
			return err
		}
		c.ws()
		if c.i >= len(c.in) || c.in[c.i] != ':' {
			return errSlow
		}
		c.i++
		c.out = append(c.out, ':')
		if err := c.value(); err != nil {
			return err
		}
		m.end = len(c.out)
		ms = append(ms, m)
		c.ws()
		if c.i >= len(c.in) {
			return errSlow
		}
		if c.in[c.i] == '}' {
			c.i++
			break
		}
		if c.in[c.i] != ',' {
			return errSlow
		}
		c.i++
		c.out = append(c.out, ',')
	}
	sorted := true // strictly: a duplicate needs the rewrite too
	for k := 1; k < len(ms); k++ {
		if ms[k-1].key >= ms[k].key {
			sorted = false
			break
		}
	}
	if !sorted {
		// stable: of equal keys the last written is the last in the run
		slices.SortStableFunc(ms, func(a, b member) int {
			switch {
			case a.key < b.key:
				return -1
			case a.key > b.key:
				return 1
			}
			return 0
		})
		c.tmp = append(c.tmp[:0], c.out[base:]...)
		c.out = c.out[:base]
		for k, m := range ms {
			if k+1 < len(ms) && ms[k+1].key == m.key {
				continue
			}
			if len(c.out) > base {
				c.out = append(c.out, ',')
			}
			c.out = append(c.out, c.tmp[m.start-base:m.end-base]...)
		}
	}
	c.out = append(c.out, '}')
	return nil
}

// scanString finds the end of the string starting at in[i] (the opening
// quote): end is just past the closing quote. plain says the encoder would
// write it back byte for byte: printable ASCII, no backslash. A string with
// a control character is malformed (err).
func scanString(in []byte, i int) (end int, plain bool, err error) {
	plain = true
	for j := i + 1; j < len(in); j++ {
		switch b := in[j]; {
		case b == '"':
			return j + 1, plain, nil
		case b == '\\':
			plain = false
			j++ // skip what it escapes; the slow path checks it
		case b < 0x20:
			return 0, false, errSlow
		case b >= 0x80:
			plain = false
		}
	}
	return 0, false, errSlow
}

// scanNumber finds the end of a JSON number at in[i]; ok is false if it
// isn't one by the grammar.
func scanNumber(in []byte, i int) (int, bool) {
	j := i
	if j < len(in) && in[j] == '-' {
		j++
	}
	switch {
	case j < len(in) && in[j] == '0':
		j++
	case j < len(in) && in[j] >= '1' && in[j] <= '9':
		for j < len(in) && in[j] >= '0' && in[j] <= '9' {
			j++
		}
	default:
		return 0, false
	}
	if j < len(in) && in[j] == '.' {
		j++
		k := j
		for j < len(in) && in[j] >= '0' && in[j] <= '9' {
			j++
		}
		if j == k {
			return 0, false
		}
	}
	if j < len(in) && (in[j] == 'e' || in[j] == 'E') {
		j++
		if j < len(in) && (in[j] == '+' || in[j] == '-') {
			j++
		}
		k := j
		for j < len(in) && in[j] >= '0' && in[j] <= '9' {
			j++
		}
		if j == k {
			return 0, false
		}
	}
	return j, true
}

// skipValue finds the end of the value starting at in[i] (after any
// whitespace), checking its grammar but building nothing.
func skipValue(in []byte, i int, depth int) (int, error) {
	i = skipWS(in, i)
	if i >= len(in) || depth > maxDepth {
		return 0, errSlow
	}
	switch b := in[i]; {
	case b == '"':
		e, _, err := scanString(in, i)
		return e, err
	case b == '-' || (b >= '0' && b <= '9'):
		e, ok := scanNumber(in, i)
		if !ok {
			return 0, errSlow
		}
		return e, nil
	case b == '{' || b == '[':
		closer := byte('}')
		if b == '[' {
			closer = ']'
		}
		i = skipWS(in, i+1)
		if i < len(in) && in[i] == closer {
			return i + 1, nil
		}
		for {
			if b == '{' {
				i = skipWS(in, i)
				if i >= len(in) || in[i] != '"' {
					return 0, errSlow
				}
				e, _, err := scanString(in, i)
				if err != nil {
					return 0, err
				}
				i = skipWS(in, e)
				if i >= len(in) || in[i] != ':' {
					return 0, errSlow
				}
				i++
			}
			e, err := skipValue(in, i, depth+1)
			if err != nil {
				return 0, err
			}
			i = skipWS(in, e)
			if i >= len(in) {
				return 0, errSlow
			}
			if in[i] == closer {
				return i + 1, nil
			}
			if in[i] != ',' {
				return 0, errSlow
			}
			i++
		}
	default:
		for _, lit := range [...]string{"true", "false", "null"} {
			if bytes.HasPrefix(in[i:], []byte(lit)) {
				return i + len(lit), nil
			}
		}
		return 0, errSlow
	}
}

func skipWS(in []byte, i int) int {
	for i < len(in) && (in[i] == ' ' || in[i] == '\t' || in[i] == '\n' || in[i] == '\r') {
		i++
	}
	return i
}

// Members reads a JSON object's top-level members without decoding their
// values: name -> the value's raw bytes, the last of duplicates. It checks
// the whole object's grammar (a value it can't vouch for is handed to
// encoding/json, which has the last word). A key with an escape is decoded.
func Members(obj []byte) (map[string][]byte, error) {
	i := skipWS(obj, 0)
	if i >= len(obj) || obj[i] != '{' {
		return nil, errors.New("not a JSON object")
	}
	end, err := skipValue(obj, i, 0)
	if err == nil && skipWS(obj, end) != len(obj) {
		err = errSlow
	}
	if err != nil {
		// let encoding/json say what is wrong (or find nothing is)
		var raw map[string]json.RawMessage
		if jerr := json.Unmarshal(obj, &raw); jerr != nil {
			return nil, jerr
		}
		out := make(map[string][]byte, len(raw))
		for k, v := range raw {
			out[k] = v
		}
		return out, nil
	}
	out := map[string][]byte{}
	i = skipWS(obj, i+1)
	if obj[i] == '}' {
		return out, nil
	}
	for {
		i = skipWS(obj, i)
		ke, plain, _ := scanString(obj, i)
		key := string(obj[i+1 : ke-1])
		if !plain {
			if err := json.Unmarshal(obj[i:ke], &key); err != nil {
				return nil, err
			}
		}
		i = skipWS(obj, ke) + 1 // the ':'
		vs := skipWS(obj, i)
		ve, _ := skipValue(obj, vs, 1)
		out[key] = obj[vs:ve]
		i = skipWS(obj, ve)
		if obj[i] == '}' {
			return out, nil
		}
		i++ // the ','
	}
}

// String decodes a raw JSON value that should be a string; ok is false if
// it is something else (or absent).
func String(raw []byte) (string, bool) {
	if len(raw) < 2 || raw[0] != '"' {
		return "", false
	}
	if e, plain, err := scanString(raw, 0); err == nil && plain && e == len(raw) {
		return string(raw[1 : len(raw)-1]), true
	}
	var s string
	if json.Unmarshal(raw, &s) != nil {
		return "", false
	}
	return s, true
}

// str writes the string at c.in[c.i] as the encoder would and returns it
// decoded (a key sorts by its decoded form). A plain one is copied; one
// with an escape or non-ASCII goes through encoding/json on its own, so a
// prompt in Japanese doesn't send the picture beside it the slow way.
func (c *canon) str() (string, error) {
	s, plain, err := scanString(c.in, c.i)
	if err != nil {
		return "", errSlow
	}
	raw := c.in[c.i:s]
	c.i = s
	if plain {
		c.out = append(c.out, raw...)
		return string(raw[1 : len(raw)-1]), nil
	}
	var v string
	if json.Unmarshal(raw, &v) != nil {
		return "", errSlow
	}
	var buf bytes.Buffer
	e := json.NewEncoder(&buf)
	e.SetEscapeHTML(false)
	if e.Encode(v) != nil {
		return "", errSlow
	}
	c.out = append(c.out, bytes.TrimRight(buf.Bytes(), "\n")...)
	return v, nil
}
