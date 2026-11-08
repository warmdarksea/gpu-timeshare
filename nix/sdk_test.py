# gpu-timeshare through the official OpenAI SDK: models, chat completions,
# the cache's headers, files and a batch mixing models.
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

lines = [{"custom_id": f"r{i}", "method": "POST", "url": "/v1/chat/completions",
          "body": {"model": "ab"[i % 2], "messages": [{"role": "user", "content": f"picture {i}"}]}}
         for i in range(6)]
f = c.files.create(file=("in.jsonl", "\n".join(json.dumps(l) for l in lines).encode()), purpose="batch")
b = c.batches.create(input_file_id=f.id, endpoint="/v1/chat/completions", completion_window="24h",
                     metadata={"who": "vm"})
deadline = time.time() + 120
while b.status not in ("completed", "failed", "expired", "cancelled"):
    assert time.time() < deadline, b
    time.sleep(1)
    b = c.batches.retrieve(b.id)
assert b.status == "completed", b
assert b.request_counts.completed == 6 and b.request_counts.failed == 0, b
assert b.metadata == {"who": "vm"}, b
out = [json.loads(l) for l in c.files.content(b.output_file_id).text.splitlines()]
assert [o["custom_id"] for o in out] == [f"r{i}" for i in range(6)], out
for i, o in enumerate(out):
    assert o["response"]["status_code"] == 200, o
    assert o["response"]["body"]["model"] == "ab"[i % 2], o
assert any(x.id == b.id for x in c.batches.list()), "the batch isn't listed"
print("sdk: ok")
