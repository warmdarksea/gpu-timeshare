package queue

import (
	"fmt"
	"strconv"
	"strings"
	"time"
)

// Policy is what a request's Cache-Control (RFC 9111) asks of the cache:
//
//	no-cache        don't answer from the cache (the answer is still stored)
//	no-store        don't answer from the cache, and don't store the answer
//	max-age=N       answer from the cache only with an answer at most N seconds old
//	only-if-cached  answer from the cache or not at all (504), never ask a model
//
// On a batch's create it applies to every line.
type Policy struct {
	Read, Write  bool
	MaxAge       time.Duration // > 0: the oldest answer the cache may give
	OnlyIfCached bool
}

func ParseCacheControl(h string) Policy {
	p := Policy{Read: true, Write: true}
	for _, d := range strings.Split(h, ",") {
		d = strings.ToLower(strings.TrimSpace(d))
		name, val, _ := strings.Cut(d, "=")
		switch strings.TrimSpace(name) {
		case "no-cache":
			p.Read = false
		case "no-store":
			p.Read, p.Write = false, false
		case "only-if-cached":
			p.OnlyIfCached = true
		case "max-age":
			n, err := strconv.ParseInt(strings.Trim(strings.TrimSpace(val), `"`), 10, 64)
			if err != nil || n < 0 {
				continue // unparseable: ignored, as a cache would
			}
			if n == 0 {
				p.Read = false // nothing cached is that fresh
			} else {
				p.MaxAge = time.Duration(n) * time.Second
			}
		}
	}
	return p
}

// CacheStatus is the Cache-Status (RFC 9211) for an answer.
//
//	hit                   from the cache (Age says how old)
//	fwd=miss; stored      asked of the model, and kept
//	fwd=request           asked of the model because the request said so (no-cache, no-store, max-age=0)
//	fwd=miss; collapsed   the same question was already being asked; this got that answer
func CacheStatus(p Policy, r Result) string {
	const name = "gpu-timeshare"
	switch {
	case r.Cached && r.CachedAt > 0:
		return name + "; hit"
	case r.Cached:
		return name + "; fwd=miss; collapsed"
	case !p.Read:
		s := name + "; fwd=request"
		if p.Write && r.Status >= 200 && r.Status < 300 {
			s += "; stored"
		}
		return s
	case p.Write && r.Status >= 200 && r.Status < 300:
		return name + "; fwd=miss; stored"
	default:
		return name + "; fwd=miss"
	}
}

// Age is the Age header's value for a cached answer.
func Age(r Result, now time.Time) string {
	if r.CachedAt <= 0 {
		return ""
	}
	a := now.Unix() - r.CachedAt
	if a < 0 {
		a = 0
	}
	return fmt.Sprint(a)
}
