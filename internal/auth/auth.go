// Package auth: clients and their bearer tokens.
//
// A token is shown once, when the client is made; the database keeps only
// its sha256. A client sees its own files and batches; an admin sees
// everyone's. Answers are cached by the question alone, so a client gets a
// cached answer only by sending the whole question -- image bytes included
// -- again: having the question is the permission.
package auth

import (
	"crypto/rand"
	"crypto/sha256"
	"crypto/subtle"
	"database/sql"
	"encoding/hex"
	"errors"
	"fmt"
	"regexp"
	"strings"
	"time"
)

const Prefix = "gts_"

type Client struct {
	Name    string
	Admin   bool
	Created time.Time
}

type Auth struct{ db *sql.DB }

func New(db *sql.DB) *Auth { return &Auth{db} }

var validName = regexp.MustCompile(`^[A-Za-z0-9][A-Za-z0-9._-]{0,63}$`)

func hash(token string) string {
	h := sha256.Sum256([]byte(token))
	return hex.EncodeToString(h[:])
}

// Add makes a client and returns its token -- the only time it's shown.
func (a *Auth) Add(name string, admin bool) (string, error) {
	if !validName.MatchString(name) {
		return "", fmt.Errorf("a client name is letters, digits, '.', '_' or '-' (at most 64)")
	}
	b := make([]byte, 32)
	if _, err := rand.Read(b); err != nil {
		return "", err
	}
	token := Prefix + hex.EncodeToString(b)
	_, err := a.db.Exec("INSERT INTO clients(name, token_sha, admin, created) VALUES (?, ?, ?, ?)",
		name, hash(token), admin, time.Now().Unix())
	if err != nil && strings.Contains(err.Error(), "UNIQUE") {
		return "", fmt.Errorf("client %q exists (remove it first to issue a new token)", name)
	}
	return token, err
}

// Remove deletes a client and the work it was waiting for. Its files and
// batches go too; cached answers stay (they belong to the questions).
func (a *Auth) Remove(name string) error {
	r, err := a.db.Exec("DELETE FROM clients WHERE name = ?", name)
	if err != nil {
		return err
	}
	if n, _ := r.RowsAffected(); n == 0 {
		return fmt.Errorf("no client %q", name)
	}
	for _, q := range []string{
		"DELETE FROM requests WHERE client = ?",
		"DELETE FROM batches WHERE client = ?",
	} {
		if _, err := a.db.Exec(q, name); err != nil {
			return err
		}
	}
	return nil
}

func (a *Auth) List() ([]Client, error) {
	rows, err := a.db.Query("SELECT name, admin, created FROM clients ORDER BY name")
	if err != nil {
		return nil, err
	}
	defer rows.Close()
	var out []Client
	for rows.Next() {
		var c Client
		var created int64
		if err := rows.Scan(&c.Name, &c.Admin, &created); err != nil {
			return nil, err
		}
		c.Created = time.Unix(created, 0)
		out = append(out, c)
	}
	return out, rows.Err()
}

var ErrUnauthorized = errors.New("unauthorized")

// Authenticate is a bearer token -> its client.
func (a *Auth) Authenticate(token string) (Client, error) {
	if !strings.HasPrefix(token, Prefix) {
		return Client{}, ErrUnauthorized
	}
	want := hash(token)
	var c Client
	var got string
	var created int64
	err := a.db.QueryRow("SELECT name, admin, created, token_sha FROM clients WHERE token_sha = ?", want).
		Scan(&c.Name, &c.Admin, &created, &got)
	if err != nil || subtle.ConstantTimeCompare([]byte(got), []byte(want)) != 1 {
		return Client{}, ErrUnauthorized
	}
	c.Created = time.Unix(created, 0)
	return c, nil
}
