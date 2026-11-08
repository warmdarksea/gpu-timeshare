# gpu-timeshare through the official OpenAI SDK: models, chat completions,
# the cache's headers, files and one batch per model.
#   TOKEN=... python3 sdk_test.py BASE_URL CA_CERT [cached]
import json
import os
import sys
import time

import httpx
import openai
from openai import OpenAI

base, ca = sys.argv[1], sys.argv[2]
cached_only = len(sys.argv) > 3
c = OpenAI(base_url=base, api_key=os.environ["TOKEN"], http_client=httpx.Client(verify=ca),
           max_retries=0, timeout=120)
hi = [{"role": "user", "content": "hi"}]

if cached_only:
    # after a restart: answered from the cache, without starting a model
    r = c.chat.completions.with_raw_response.create(model="a", messages=hi,
                                                    extra_headers={"Cache-Control": "only-if-cached"})
    assert r.headers["cache-status"] == "gpu-timeshare; hit", r.headers
    print("sdk (cached): ok")
    sys.exit(0)

names = sorted(m.id for m in c.models.list())
assert names == ["a", "b", "p"], names

r = c.chat.completions.with_raw_response.create(model="a", messages=hi)
cc = r.parse()
assert cc.model == "a", cc
assert cc.choices[0].message.content.startswith("upstream-a saw"), cc
assert r.headers["cache-status"] == "gpu-timeshare; fwd=miss; stored", r.headers
r = c.chat.completions.with_raw_response.create(model="a", messages=hi)
assert r.headers["cache-status"] == "gpu-timeshare; hit", r.headers
assert "age" in r.headers, r.headers

try:
    c.chat.completions.create(model="b", messages=[{"role": "user", "content": "never asked"}],
                              extra_headers={"Cache-Control": "only-if-cached"})
    raise SystemExit("only-if-cached asked a model")
except openai.APIStatusError as e:
    assert e.status_code == 504, e

try:
    c.chat.completions.create(model="nope", messages=hi)
    raise SystemExit("an unknown model answered")
except openai.NotFoundError:
    pass

p = c.chat.completions.create(model="p", messages=hi)
assert p.choices[0].message.content.startswith("upstream-p saw"), p

# one batch per model, as with OpenAI; both queued at once
batches = {}
for model in ("a", "b"):
    lines = [{"custom_id": f"{model}{i}", "method": "POST", "url": "/v1/chat/completions",
              "body": {"model": model, "messages": [{"role": "user", "content": f"picture {i}"}]}}
             for i in range(3)]
    f = c.files.create(file=(f"{model}.jsonl", "\n".join(json.dumps(l) for l in lines).encode()), purpose="batch")
    batches[model] = c.batches.create(input_file_id=f.id, endpoint="/v1/chat/completions",
                                      completion_window="24h", metadata={"who": "vm"})

# a batch mixing models fails validation, as OpenAI's would
mixed = [{"custom_id": m, "method": "POST", "url": "/v1/chat/completions",
          "body": {"model": m, "messages": hi}} for m in ("a", "b")]
f = c.files.create(file=("mixed.jsonl", "\n".join(json.dumps(l) for l in mixed).encode()), purpose="batch")
bad = c.batches.create(input_file_id=f.id, endpoint="/v1/chat/completions", completion_window="24h")
assert bad.status == "failed" and bad.errors.data[0].code == "mismatched_model", bad

deadline = time.time() + 120
for model, b in batches.items():
    while b.status not in ("completed", "failed", "expired", "cancelled"):
        assert time.time() < deadline, b
        time.sleep(1)
        b = c.batches.retrieve(b.id)
    assert b.status == "completed", b
    assert b.request_counts.completed == 3 and b.request_counts.failed == 0, b
    assert b.metadata == {"who": "vm"}, b
    out = [json.loads(l) for l in c.files.content(b.output_file_id).text.splitlines()]
    assert [o["custom_id"] for o in out] == [f"{model}{i}" for i in range(3)], out
    for o in out:
        assert o["response"]["status_code"] == 200, o
        assert o["response"]["body"]["model"] == model, o
    assert any(x.id == b.id for x in c.batches.list()), "the batch isn't listed"
print("sdk: ok")
