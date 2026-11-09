# Security

This document describes:

1. the security model: what is isolated from what, and how (§1–§4), and
   what is not isolated (§5);
2. how to examine the isolation at runtime with systemd tools (§6);
3. how to examine it without systemd tools, from the kernel (§7).

It applies to the NixOS module, [`nix/module.nix`](../nix/module.nix).

## 1. Threats

| Item | Trust | Why |
|---|---|---|
| root, the NixOS configuration | trusted | They define the sandbox. |
| the `gpu-timeshare` service | partly trusted | It holds the token hashes, the queue, the cache and the uploads. It must not get more access than that. |
| a model process | **not trusted** | It runs third-party code: Python wheels, model code, kernels compiled at runtime. Weights and requests from clients go into it. |
| a client | **not trusted** | It has a token. It must see only its own files and batches. |

The design goal: a model process that an attacker controls cannot read
or change gpu-timeshare's data, other models' data, the host's files or
the network. It can only answer (or not answer) the requests it gets.

## 2. Model units

Each model with `isolation = "unit"` (the default) is a systemd service,
`gpu-timeshare-model-NAME`. Only gpu-timeshare starts and stops it.

| Setting | Effect |
|---|---|
| `User=gtm-NAME`, `Group=gtm-NAME` | A system user for each model. Models cannot read each other's files. Not `DynamicUser`: systemd 262 mounts a `DynamicUser` cache directory `noexec`, and the models compile GPU kernels there and load them. |
| `ProtectSystem=strict` | The file system is read-only. |
| `CacheDirectory=gpu-timeshare-model-cache/NAME` | The one persistent directory it can write. It can run what it writes there (compiled kernels). |
| `ReadWritePaths=/run/gpu-timeshare-models` | Where it creates its socket. |
| `PrivateTmp=true` | Its own `/tmp` and `/var/tmp`. |
| `ProtectHome=true` | No `/home`, `/root`, `/run/user`. |
| `InaccessiblePaths=/var/lib/gpu-timeshare /var/cache/gpu-timeshare` | No access to gpu-timeshare's state and cache, whatever the file permissions are. |
| `PrivateNetwork=true`, `IPAddressDeny=any` | Its own network namespace with only a loopback interface. It cannot reach the host's loopback services or the network. (`network = true` removes this.) |
| socket in `/run/gpu-timeshare-models`, mode 2770, group `gpu-timeshare-models`, `UMask=0007` | Only gpu-timeshare (and root) can connect to the model. |
| `DevicePolicy=closed`, `DeviceAllow=char-nvidia… rw` | Only the nvidia device nodes. A model with `gpu = false` gets `PrivateDevices=true` (no devices at all). |
| `CapabilityBoundingSet=` (empty), `NoNewPrivileges=true`, `RestrictSUIDSGID=true` | No capabilities, now or later. Setuid programs give it nothing. |
| `SystemCallFilter=@system-service`, `SystemCallArchitectures=native` | A seccomp filter: the system calls a normal service uses. |
| `RestrictAddressFamilies=AF_UNIX AF_INET AF_INET6 AF_NETLINK` | No raw sockets, no packet sockets, no other families. |
| `RestrictNamespaces=true` | It cannot make new namespaces (no containers inside). |
| `ProtectKernelTunables`, `ProtectKernelModules`, `ProtectKernelLogs`, `ProtectControlGroups`, `ProtectClock`, `ProtectHostname`, `LockPersonality`, `RestrictRealtime` | No changes to the kernel, its modules, its logs, the cgroup tree, the clock or the host name. |
| `ProtectProc=invisible` | In `/proc` it sees only its own processes. |
| `KillMode=control-group` | A stop kills every process of the model, so no process keeps GPU memory. |
| `RemoveIPC=true` | Its System V IPC objects are removed when it stops. |

A model that only listens on TCP (`{port}`) listens on its private
loopback. `systemd-socket-proxyd` runs in the same network namespace
(`JoinsNamespaceOf=`) and relays the socket to it.

## 3. The gpu-timeshare service

| Setting | Effect |
|---|---|
| `User=gpu-timeshare` | Its own user. Its state directory has mode 0700. |
| a polkit rule | It can start, stop and reset its own model units. It cannot do anything else through systemd. |
| `ProtectSystem=strict`, `ProtectHome=true`, `PrivateTmp=true` | Read-only file system except its state, its cache and the socket directory. |
| `CapabilityBoundingSet=` (empty), `NoNewPrivileges=true` | No capabilities. |
| `PrivateDevices=true` | No devices, unless a model has `isolation = "process"` and `gpu = true`. |

A model with `isolation = "process"` runs as a child process of
gpu-timeshare, in gpu-timeshare's sandbox. It can read gpu-timeshare's
state. Use it only for code you trust.

## 4. Clients

- A client sends a bearer token. gpu-timeshare keeps only its SHA-256.
- A client sees only its own files and batches. An admin sees all.
- Answers are shared through the cache. To get a cached answer, a client
  must send the whole question again, image bytes included.
- Off loopback, TLS is on. Without a certificate, gpu-timeshare makes a
  self-signed one. On loopback, use SSH port forwarding from other hosts.

## 5. Known gaps

These are not isolated. The output of `sandbox-report` (§7) shows them.

- **PID namespace.** The model uses the host's. `ProtectProc=invisible`
  hides other users' processes in `/proc`.
- **IPC namespace.** The model uses the host's. System V IPC objects are
  protected only by their permissions.
- **`/dev/shm` of GPU models.** A model with `gpu = true` sees the host's
  `/dev`, so it shares `/dev/shm` (mode 1777) with the host.
- **Memory.** There is no memory limit by default. Set
  `serviceConfig.MemoryMax` for each model.
- **Readable files.** The file system is read-only, not hidden. A model
  can read every world-readable file (`/etc`, `/nix/store`).
- **GPU memory.** We did not examine if the driver clears GPU memory
  between two models.
- **Seccomp.** `@system-service` is a large set of system calls.

## 6. Examine it with systemd tools

These tools show the configuration that systemd uses. They do not show
what the kernel does. §7 shows that.

| Command | What it shows |
|---|---|
| `systemctl cat gpu-timeshare-model-qwen` | The unit file, as NixOS wrote it. |
| `systemctl show gpu-timeshare-model-qwen -p User,ProtectSystem,PrivateNetwork,DevicePolicy,DeviceAllow,CapabilityBoundingSet,NoNewPrivileges,InaccessiblePaths,ReadWritePaths,CacheDirectory` | The settings that systemd uses, after all defaults. |
| `systemd-analyze security gpu-timeshare-model-qwen` | Each sandbox setting, and an "exposure" score from 0 (best) to 10. |
| `systemd-analyze syscall-filter @system-service` | The system calls in the filter. |
| `systemd-cgls -u gpu-timeshare-model-qwen.service` | The processes in the unit. |
| `cat /etc/polkit-1/rules.d/*.rules` | The polkit rule for gpu-timeshare. |
| `sudo -u gpu-timeshare systemctl stop nscd` | Must fail: the polkit rule allows only the model units. |

To test one setting without a model, run a command with only that setting:

```sh
sudo systemd-run --wait --pipe -p DevicePolicy=closed \
  -p 'DeviceAllow=char-nvidia rw' -p 'DeviceAllow=char-nvidiactl rw' -p 'DeviceAllow=char-nvidia-uvm rw' \
  nvidia-smi -L
```

If it prints the GPU, the device rules let a model use the GPU.

## 7. Examine it without systemd tools

[`bin/sandbox-report`](../bin/sandbox-report) shows what a running
process can reach. It reads every fact from the kernel (`/proc`, `/sys`).
It does not ask the process. It needs root.

```sh
# any process of the unit: they all have the same sandbox
pid=$(head -1 /sys/fs/cgroup/system.slice/gpu-timeshare-model-qwen.service/cgroup.procs)
sudo bin/sandbox-report $pid                 # what the kernel says
sudo bin/sandbox-report $pid --probe \
  --path /var/lib/gpu-timeshare --path /etc/shadow   # and a test as the process
```

`bin/sandbox-report` runs with `nix-shell`. `nix-build -A sandbox-report`
makes a version that does not need `nix-shell`.

### What it reads

| Part | Source | What it tells |
|---|---|---|
| process | `/proc/PID/status`, `/proc/PID/exe` | Executable, real/effective uid and gid, groups. |
| privileges | `/proc/PID/status` (`CapEff`, `CapBnd`, `NoNewPrivs`, `Seccomp`) | Capabilities by name; if setuid can give it more; if a seccomp filter is on. |
| namespaces | `/proc/PID/ns/*` compared with `/proc/1/ns/*` | For each namespace: the host's, or its own (and which other processes share it). |
| files | `/proc/PID/mountinfo` | If the mount namespace is the host's: "every file its uid and groups can reach". If not: `/` read-only or not, each writable mount (and if it is `noexec`), the paths made inaccessible, the `/proc` options. |
| network | `/proc/PID/net/{dev,fib_trie,if_inet6,tcp,tcp6}` | Interfaces, addresses and listening sockets in its network namespace. |
| devices | `/proc/PID/root/dev` | The device nodes it can see. |
| cgroup | `/proc/PID/cgroup`, `/sys/fs/cgroup/…/{memory,pids,cpu,io}.*`, `/proc/PID/limits` | Its cgroup, the limits on it, its resource limits. |
| open now | `/proc/PID/fd` | What it has open: files, sockets, devices. |

### The probe

With `--probe`, a helper process:

1. joins the target's cgroup (so the cgroup device policy applies to it);
2. joins the target's IPC, UTS, network, cgroup and mount namespaces;
3. takes the target's uid, gid and groups (and so loses all capabilities).

Then it:

- opens each device node it can see (read-write, else read-only), and says
  if the device policy or the file permissions stop it;
- tests which writable mounts it can write to;
- tests read, write and execute on each `--path`.

The probe does not copy the seccomp filter or the capabilities of the
target. For a process with capabilities, it shows less access than the
process has. The probe never opens a watchdog device: that would start
the hardware watchdog.

### Example

`gpu-timeshare-model-b` in the VM test (`nix/test.nix`, a model with
`gpu = false`; the test checks these lines):

```
user        gtm-b (996)
groups      gtm-b (995), gpu-timeshare-models (997)
capabilities  effective: none
no_new_privs  yes: setuid files and file capabilities give it nothing
seccomp       filter, 31 filter(s) (not decoded here)
mnt     own mnt:[4026532550]; shared with 1 other process(es): 974 coreutils
net     own net:[4026532494]; shared with 2 other process(es): ..., 975 systemd-socket-proxyd
pid     the host's
ipc     the host's
48 mounts. / is read-only.
made inaccessible: /home, ..., /var/cache/gpu-timeshare, /var/lib/gpu-timeshare
/proc at /proc: hidepid=invisible
interfaces: lo
listening in this namespace: tcp 127.0.0.1:8000
devices it can open: /dev/full (rw), /dev/null (rw), ..., /dev/zero (rw)
mounts it can write to: /dev/shm, /run/gpu-timeshare-models, /tmp, /var/cache/gpu-timeshare-model-cache/b, /var/tmp
/var/lib/gpu-timeshare: ---
/etc/hostname: r--
```

### Limits of the script

- It does not decode the seccomp filter. It shows only that a filter is on.
- It does not decode the cgroup device policy (a BPF program). `--probe`
  tests it.
- During `--probe`, the helper is in the target's cgroup for a short time.
  It counts against the cgroup's limits. If the unit stops, the helper
  stops too.
