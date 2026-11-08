package queue

import (
	"bytes"
	"encoding/json"

	"gpu-timeshare/internal/config"
)

// Present turns an answer as the model gave it (and as the cache keeps it)
// into what the client sees: "model" is the name the client asked for, not
// the upstream's (vllm reports its weights' path), and system_fingerprint
// is the model's fingerprint when one is configured -- what OpenAI's field
// is for: which backend configuration produced this answer.
func Present(m *config.Model, name string, body []byte) []byte {
	var obj map[string]json.RawMessage
	if json.Unmarshal(body, &obj) != nil {
		return body
	}
	if _, ok := obj["model"]; ok {
		obj["model"], _ = json.Marshal(name)
	}
	if m != nil && m.Fingerprint != "" {
		obj["system_fingerprint"], _ = json.Marshal(m.Fingerprint)
	}
	out, err := Marshal(obj)
	if err != nil {
		return body
	}
	return out
}

// Marshal is json.Marshal without escaping <, > and & (which it would do
// even inside a json.RawMessage, changing a reply's bytes for nothing).
func Marshal(v any) ([]byte, error) {
	var buf bytes.Buffer
	e := json.NewEncoder(&buf)
	e.SetEscapeHTML(false)
	if err := e.Encode(v); err != nil {
		return nil, err
	}
	return bytes.TrimRight(buf.Bytes(), "\n"), nil
}
