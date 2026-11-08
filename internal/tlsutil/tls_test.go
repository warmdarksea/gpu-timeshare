package tlsutil

import (
	"net"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// serve's way: a real ServeTLS listener; clients trust the self-signed
// certificate itself; replacing the files swaps it without a restart; a
// half-written pair keeps the old one.
func TestTLS(t *testing.T) {
	dir := t.TempDir()
	crt, key := filepath.Join(dir, "a.crt"), filepath.Join(dir, "a.key")
	if err := CertCmd([]string{"--hosts", "127.0.0.1,localhost", "--cert", crt, "--key", key}); err != nil {
		t.Fatal(err)
	}
	if st, _ := os.Stat(key); st.Mode().Perm() != 0o600 {
		t.Errorf("the key is %v, want 0600", st.Mode().Perm())
	}
	if err := CertCmd([]string{"--hosts", "x", "--cert", crt, "--key", key}); err == nil {
		t.Error("cert overwrote an existing key")
	}
	if err := CertCmd([]string{"--hosts", "x", "--cert", crt, "--key", key, "--if-missing"}); err != nil {
		t.Errorf("--if-missing with the certificate there: %v", err)
	}
	r, err := NewReloader(crt, key, t.Logf)
	if err != nil {
		t.Fatal(err)
	}
	ln, _ := net.Listen("tcp", "127.0.0.1:0")
	srv := &http.Server{TLSConfig: r.Config(), Handler: http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {})}
	go srv.ServeTLS(ln, "", "")
	defer srv.Close()
	url := "https://" + ln.Addr().String() + "/"
	get := func(cacert string) error {
		tr := &http.Transport{}
		if cacert != "" {
			c, err := ClientTLS(cacert)
			if err != nil {
				return err
			}
			tr.TLSClientConfig = c
		}
		res, err := (&http.Client{Transport: tr}).Get(url)
		if err == nil {
			res.Body.Close()
		}
		return err
	}
	if err := get(""); err == nil || !strings.Contains(err.Error(), "certificate") {
		t.Errorf("without the certificate: %v", err)
	}
	if err := get(crt); err != nil {
		t.Fatalf("with it: %v", err)
	}
	time.Sleep(10 * time.Millisecond)
	os.Remove(crt)
	os.Remove(key)
	if err := CertCmd([]string{"--hosts", "127.0.0.1", "--cert", crt + ".new", "--key", key}); err != nil {
		t.Fatal(err)
	}
	os.Rename(crt+".new", crt)
	if err := get(crt); err != nil {
		t.Errorf("after a renewal, trusting only the new one: %v", err)
	}
	renewed := filepath.Join(dir, "renewed.crt")
	data, _ := os.ReadFile(crt)
	os.WriteFile(renewed, data, 0o644)
	time.Sleep(10 * time.Millisecond)
	os.WriteFile(crt, data[:len(data)/2], 0o644)
	if err := get(renewed); err != nil {
		t.Errorf("with a half-written certificate on disk: %v", err)
	}
}
