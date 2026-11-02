#!/usr/bin/env python3
"""Standalone, Linux-only bounded Lake worker; also serves its compiler wrapper.

The worker and its resource controller deploy as immutable standalone files.
Each invocation owns one process group and holds its workspace lock until empty.
"""
from __future__ import annotations

import argparse
import ctypes
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone

MIB = 1024 * 1024
MEMORY_UNIT_MIB = 256
FRONTEND_OVERHEAD_MIB = 1024
MEMORY_BUDGET_PERCENT = 90
ELASTIC_MODULE = "lean_remote_elastic.py"
STORAGE_MODULE = "lean_remote_storage.py"
RESOURCE_DEFAULTS = {
    "build": (8, 4, 12800, 110592),
    "lint": (1, 4, 24576, 32768),
    "cache": (1, 4, 24576, 32768),
    "plan": (1, 4, 24576, 32768),
    "phase": (8, 4, 12800, 110592),
}
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")
LIBRARY_ROOT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
METADATA = {"--githash", "--version", "--short-version", "-v", "-V",
            "--print-prefix", "--print-libdir", "--help", "-h"}


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def within(path: Path, root: Path) -> Path:
    resolved = path.resolve()
    if not resolved.is_relative_to(root.resolve()) or resolved == root.resolve():
        raise ValueError(f"path must be strictly within {root}: {path}")
    return resolved


def cpu_quota(text: str) -> float | None:
    quota, period = text.split()
    if int(period) <= 0:
        raise ValueError("invalid cpu.max period")
    if quota == "max":
        return None
    value = int(quota) / int(period)
    if value <= 0:
        raise ValueError("invalid cpu.max quota")
    return value


def memory_limit(text: str) -> int | None:
    value = text.strip()
    if value == "max":
        return None
    result = int(value)
    if result <= 0:
        raise ValueError("invalid memory.max")
    return result


def cgroup_directory(proc: Path = Path("/proc")) -> tuple[Path, Path]:
    """Return this process's cgroup v2 directory and visible mount root."""
    membership = next((line[3:] for line in (proc / "self/cgroup").read_text().splitlines()
                       if line.startswith("0::")), None)
    if membership is None:
        raise ValueError("cgroup v2 membership is required")
    for line in (proc / "self/mountinfo").read_text().splitlines():
        before, after = line.split(" - ", 1)
        if after.split()[0] != "cgroup2":
            continue
        fields = before.split()
        decode = lambda value: re.sub(r"\\([0-7]{3})", lambda m: chr(int(m[1], 8)), value)
        root, mount = Path(decode(fields[3])), Path(decode(fields[4]))
        member = Path(membership)
        if member.is_relative_to(root):
            return mount / member.relative_to(root), mount
    raise ValueError("cannot locate the effective cgroup v2 mount")


def resource_limits(proc: Path = Path("/proc")) -> dict:
    current, mount = cgroup_directory(proc)
    memory_values, cpu_values, observations = [], [], []
    directory = current
    while True:
        entry = {"path": str(directory)}
        for name, parse, values in (("memory.max", memory_limit, memory_values),
                                    ("cpu.max", cpu_quota, cpu_values)):
            path = directory / name
            if path.exists():
                text = path.read_text().strip()
                entry[name] = text
                parsed = parse(text)
                if parsed is not None:
                    values.append(parsed)
        observations.append(entry)
        if directory == mount:
            break
        directory = directory.parent
        if not directory.is_relative_to(mount):
            raise ValueError("invalid cgroup ancestry")
    memtotal = next(int(line.split()[1]) * 1024 for line in (proc / "meminfo").read_text().splitlines()
                    if line.startswith("MemTotal:"))
    affinity = sorted(os.sched_getaffinity(0))
    if not affinity:
        raise ValueError("empty CPU affinity")
    return {"effective_cpus": min([float(len(affinity)), *cpu_values]),
            "memory_bytes": min([memtotal, *memory_values]), "affinity": affinity,
            "cgroup": str(current), "cgroup_limits": observations}


def validate_profile(jobs: int, threads: int, heap: int, rss: int, limits: dict, *,
                     allow_cpu_oversubscription: bool = False) -> None:
    if min(jobs, threads, heap, rss) <= 0:
        raise ValueError("all resource settings must be positive")
    if allow_cpu_oversubscription and threads != 1:
        raise ValueError("CPU oversubscription requires single-threaded frontends")
    cpu_budget = limits["effective_cpus"] * (2 if allow_cpu_oversubscription else 1)
    if jobs * threads > cpu_budget:
        raise ValueError("jobs * threads exceeds the permitted effective CPU budget")
    if rss * MIB * 100 > limits["memory_bytes"] * MEMORY_BUDGET_PERCENT:
        raise ValueError(f"RSS cutoff exceeds {MEMORY_BUDGET_PERCENT}% of effective memory")
    if heap >= rss:
        raise ValueError("per-compiler heap must be below aggregate RSS cutoff")


def apply_resource_defaults(args: argparse.Namespace) -> None:
    action = "cache" if args.action == "phase" and getattr(args, "forbid_compilation", False) else args.action
    for name, value in zip(("jobs", "threads", "lean_memory_mib", "rss_limit_mib"),
                           RESOURCE_DEFAULTS[action]):
        if getattr(args, name, None) is None:
            setattr(args, name, value)
    if args.action != "build" and args.allow_cpu_oversubscription:
        raise ValueError("CPU oversubscription is supported only for build")


def validate_inputs(base: Path, workspace: Path, run_dir: Path, action: str,
                    modules: list[str], *, allow_library_roots: bool = False
                    ) -> tuple[Path, Path, list[Path]]:
    if allow_library_roots and action != "build":
        raise ValueError("--allow-library-roots is supported only for build")
    for path in (base, workspace, run_dir):
        if not path.is_absolute():
            raise ValueError(f"an absolute path is required: {path}")
    base = base.resolve(strict=True)
    workspace = within(workspace, base / "workspaces")
    run_dir = within(run_dir, base / "logs")
    if not workspace.is_dir():
        raise ValueError("workspace does not exist")
    if run_dir.exists():
        raise ValueError("run directory must be new")
    pins = [workspace / "lean-toolchain", workspace / "lake-manifest.json"]
    lakefiles = [workspace / name for name in ("lakefile.lean", "lakefile.toml")
                 if (workspace / name).is_file()]
    if not all(path.is_file() for path in pins) or not lakefiles:
        raise ValueError("workspace needs lean-toolchain, lakefile and lake-manifest.json")
    if not modules or len(set(modules)) != len(modules):
        raise ValueError("supply distinct explicit qualified modules")
    roots = [workspace]
    if action == "cache" and (workspace / ".lake/packages").is_dir():
        roots += sorted(p for p in (workspace / ".lake/packages").iterdir() if p.is_dir())
    sources = []
    for module in modules:
        if not (MODULE.fullmatch(module) or
                (allow_library_roots and LIBRARY_ROOT.fullmatch(module))):
            raise ValueError(f"expected an explicit qualified module, not a library or option: {module}")
        relative = Path(*module.split(".")).with_suffix(".lean")
        candidates = [root / relative for root in roots if (root / relative).is_file()]
        if not candidates:
            raise ValueError(f"module source is missing from the selected workspace: {module}")
        source = within(candidates[0], workspace)
        sources.append(source)
    return workspace, run_dir, [*pins, *lakefiles, *sources]


def compiler_args(args: list[str], threads: int, heap: int) -> list[str]:
    """Replace only resource flags; preserve all mathematical options verbatim."""
    output, index = [], 0
    while index < len(args):
        arg = args[index]
        if arg in ("--", "--run", "-r"):
            return output + [f"-j{threads}", f"-M{heap}"] + args[index:]
        if arg in ("-j", "--threads", "-M", "--memory"):
            if index + 1 == len(args):
                raise ValueError(f"missing resource argument: {arg}")
            index += 2
            continue
        if arg.startswith(("--threads=", "--memory=")) or re.fullmatch(r"-[jM].+", arg):
            index += 1
            continue
        output.append(arg)
        index += 1
    return output + [f"-j{threads}", f"-M{heap}"]


def event(path: Path, kind: str, **fields) -> None:
    data = {"event": kind, "time": now(), "monotonic": time.monotonic(),
            "wrapper_pid": os.getpid(), "pgid": os.getpgrp(), **fields}
    encoded = (json.dumps(data, separators=(",", ":")) + "\n").encode()
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
    try:
        if os.write(fd, encoded) != len(encoded):
            raise OSError("short compiler event write")
    finally:
        os.close(fd)


def close_leases(leases: list) -> None:
    # Close, never LOCK_UN: an inherited duplicate belongs to the live child.
    for lease in reversed(leases):
        lease.close()


def wait_lock(path: Path, mode: int, cancelled: list[int]):
    lock = path.open("a")
    try:
        while not cancelled:
            try:
                fcntl.flock(lock, mode | fcntl.LOCK_NB)
                return lock
            except BlockingIOError:
                time.sleep(0.1)
        raise ValueError("cancelled while waiting for execution lock")
    except BaseException:
        lock.close()
        raise


def workspace_lock_path(base: Path, workspace: Path) -> Path:
    identity = hashlib.sha256(str(workspace.resolve().parent).encode()).hexdigest()
    return base / "locks" / f"workspace-{identity}.lock"


def acquire_run_locks(base: Path, workspace: Path, action: str, cancelled: list[int]) -> list:
    """Shared legacy barrier, exclusive source-container ownership, optional cache gate."""
    (base / "locks").mkdir(exist_ok=True)
    leases = []
    try:
        leases.append(wait_lock(base / "build.lock", fcntl.LOCK_SH, cancelled))
        leases.append(wait_lock(workspace_lock_path(base, workspace), fcntl.LOCK_EX, cancelled))
        if action == "cache":
            leases.append(wait_lock(base / "locks/cache-fetch.lock", fcntl.LOCK_EX, cancelled))
        return leases
    except BaseException:
        close_leases(leases)
        raise


def resource_pool_basis(limits: dict) -> dict:
    basis = {"schema_version": 1, "cpu_half_units": int(limits["effective_cpus"] * 2),
             "memory_units": limits["memory_bytes"] * MEMORY_BUDGET_PERCENT // (100 * MEMORY_UNIT_MIB * MIB),
             "memory_unit_mib": MEMORY_UNIT_MIB, "frontend_overhead_mib": FRONTEND_OVERHEAD_MIB,
             "cgroup": limits.get("cgroup"), "affinity": limits.get("affinity")}
    if min(basis["cpu_half_units"], basis["memory_units"]) < 1:
        raise ValueError("effective resources are too small for frontend admission")
    return basis


def prepare_pool(base: Path, limits: dict, cancelled: list[int]) -> dict:
    directory = base / "admission-v1"
    directory.mkdir(exist_ok=True)
    for kind in ("cpu", "memory"):
        (directory / kind).mkdir(exist_ok=True)
    basis = resource_pool_basis(limits)
    gate = wait_lock(directory / "gate.lock", fcntl.LOCK_EX, cancelled)
    try:
        path = directory / "basis.json"
        if path.exists():
            if json.loads(path.read_text()) != basis:
                raise ValueError("global admission resource basis differs; refuse to resize a live pool")
        else:
            if any(any((directory / kind).iterdir()) for kind in ("cpu", "memory")):
                raise ValueError("global admission basis missing beside existing tokens")
            write_receipt(path, basis)
    finally:
        gate.close()
    return {"directory": str(directory), "basis": basis}


def elastic_component():
    checksum = sha256(Path(__file__).with_name(ELASTIC_MODULE))
    if ELASTIC_MODULE != "lean_remote_elastic.py" and ELASTIC_MODULE != "lean_remote_elastic-" + checksum + ".py":
        raise ValueError("deployed elastic controller differs from its immutable identity")
    name = "_r5_remote_elastic_" + checksum
    if name not in sys.modules:
        spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(ELASTIC_MODULE))
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        try:
            spec.loader.exec_module(module)
        except BaseException:
            sys.modules.pop(name, None)
            raise
    return sys.modules[name]


def storage_component():
    path = Path(__file__).with_name(STORAGE_MODULE)
    checksum = sha256(path)
    if STORAGE_MODULE != "lean_remote_storage.py" and STORAGE_MODULE != "lean_remote_storage-" + checksum + ".py":
        raise ValueError("deployed storage helper differs from its immutable identity")
    name = "_r5_remote_storage_" + checksum
    if name not in sys.modules:
        spec = importlib.util.spec_from_file_location(name, path)
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        try:
            spec.loader.exec_module(module)
        except BaseException:
            sys.modules.pop(name, None)
            raise
    return sys.modules[name]


def migration_frontends(base: Path, proc: Path = Path("/proc")) -> list[int]:
    """Unleased native descendants must also settle before retiring old admission."""
    found = []
    for directory in proc.iterdir():
        if not directory.name.isdecimal():
            continue
        try:
            if (directory / "comm").read_text().strip() not in {"lean", "leanchecker"}:
                continue
            executable = Path(os.readlink(directory / "exe"))
            if executable.is_relative_to(base):
                found.append(int(directory.name))
        except (FileNotFoundError, ProcessLookupError):
            continue
    return found


def prepare_elastic_pool(base: Path, limits: dict, cancelled: list[int]) -> dict:
    """Retire fixed admission only at idle; never invalidate a running old actor."""
    directory = base / "admission-v1"
    directory.mkdir(exist_ok=True)
    for kind in ("cpu", "memory"):
        (directory / kind).mkdir(exist_ok=True)
    previous = resource_pool_basis(limits)
    basis = dict(previous, schema_version=2, admission_policy="elastic-sampled-v1")
    path = directory / "basis.json"
    while not cancelled:
        if path.exists() and json.loads(path.read_text()) == basis:
            return {"directory": str(directory), "basis": basis}
        leases = []
        try:
            legacy = (base / "build.lock").open("a")
            leases.append(legacy)
            fcntl.flock(legacy, fcntl.LOCK_EX | fcntl.LOCK_NB)
            gate = (directory / "gate.lock").open("a")
            leases.append(gate)
            fcntl.flock(gate, fcntl.LOCK_EX | fcntl.LOCK_NB)
            current = json.loads(path.read_text()) if path.exists() else None
            if current not in (None, previous, basis):
                raise ValueError("unknown admission basis; reconcile its resource owner before migration")
            if current is None and any(any((directory / kind).iterdir()) for kind in ("cpu", "memory")):
                raise ValueError("admission basis missing beside existing tokens; reconcile before migration")
            for kind in ("cpu", "memory"):
                for token_path in (directory / kind).iterdir():
                    token = token_path.open("a")
                    leases.append(token)
                    fcntl.flock(token, fcntl.LOCK_EX | fcntl.LOCK_NB)
            if migration_frontends(base):
                raise BlockingIOError("old or unleased compiler still running")
            write_receipt(path, basis)
            return {"directory": str(directory), "basis": basis}
        except BlockingIOError:
            pass
        finally:
            close_leases(leases)
        time.sleep(0.1)
    raise ValueError("cancelled while waiting for idle elastic admission migration")


def frontend_request(threads: int, heap: int, oversubscription: bool = False) -> dict:
    if min(threads, heap) < 1 or (oversubscription and threads != 1):
        raise ValueError("invalid frontend admission request")
    memory = (heap + FRONTEND_OVERHEAD_MIB + MEMORY_UNIT_MIB - 1) // MEMORY_UNIT_MIB
    return {"cpu_half_units": 1 if oversubscription else threads * 2,
            "memory_units": memory, "memory_reserved_mib": memory * MEMORY_UNIT_MIB}


def process_tree_request(jobs: int, threads: int, rss: int) -> dict:
    cores = jobs * threads
    units = (rss + MEMORY_UNIT_MIB - 1) // MEMORY_UNIT_MIB
    return {"cpu_half_units": cores * 2, "whole_cpu_cores": cores,
            "memory_units": units, "memory_reserved_mib": units * MEMORY_UNIT_MIB}


def wait_admission(pool: dict, request: dict, cancelled: list[int]) -> list:
    while not cancelled:
        leases = try_admit(pool, request)
        if leases is not None:
            return leases
        time.sleep(0.1)
    raise ValueError("cancelled while waiting for global resource admission")


def validate_admission(pool: dict, request: dict) -> None:
    for name in ("cpu_half_units", "memory_units"):
        if not 0 < request[name] <= pool["basis"][name]:
            raise ValueError(f"frontend request exceeds global admission {name}")


def try_admit(pool: dict, request: dict) -> list | None:
    """Acquire the complete CPU+memory request atomically, or keep no tokens."""
    validate_admission(pool, request)
    directory = Path(pool["directory"])
    leases = []
    gate = (directory / "gate.lock").open("a")
    try:
        try:
            fcntl.flock(gate, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return None
        if json.loads((directory / "basis.json").read_text()) != pool["basis"]:
            raise ValueError("global admission basis changed during this run")
        for kind, name in (("cpu", "cpu_half_units"), ("memory", "memory_units")):
            remaining = request[name]
            if kind == "cpu" and "whole_cpu_cores" in request:
                if remaining != request["whole_cpu_cores"] * 2:
                    raise ValueError("whole-core CPU request differs from its token weight")
                for core in range(pool["basis"][name] // 2):
                    pair = []
                    for index in (core * 2, core * 2 + 1):
                        token = (directory / kind / str(index)).open("a")
                        try:
                            fcntl.flock(token, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        except BlockingIOError:
                            token.close()
                            close_leases(pair)
                            pair = []
                            break
                        pair.append(token)
                    if pair:
                        leases.extend(pair)
                        remaining -= 2
                        if remaining == 0:
                            break
                if remaining:
                    close_leases(leases)
                    return None
                continue
            for index in range(pool["basis"][name]):
                token = (directory / kind / str(index)).open("a")
                try:
                    fcntl.flock(token, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    token.close()
                    continue
                leases.append(token)
                remaining -= 1
                if remaining == 0:
                    break
            if remaining:
                close_leases(leases)
                return None
        return leases
    except BaseException:
        close_leases(leases)
        raise
    finally:
        gate.close()


def admitted_affinity(pool: dict, leases: list) -> list[int]:
    directory = Path(pool["directory"]) / "cpu"
    cores = sorted({int(Path(lease.name).name) // 2 for lease in leases
                    if Path(lease.name).parent == directory})
    return [pool["basis"]["affinity"][core] for core in cores]


def spawn_owned(command: list[str], *, affinity: list[int] | None = None, **kwargs):
    # Inherit the mask at fork, then restore the single-threaded supervisor.
    # This avoids Python preexec callbacks and adds no bootstrap process.
    if affinity is None:
        return subprocess.Popen(command, **kwargs)
    previous = os.sched_getaffinity(0)
    os.sched_setaffinity(0, affinity)
    try:
        return subprocess.Popen(command, **kwargs)
    finally:
        os.sched_setaffinity(0, previous)


def supervisor_holds_scope(config: dict, proc: Path = Path("/proc")) -> bool:
    """Whole-tree fallback for ordinary tools that close inherited descriptors."""
    owner = config.get("scope_supervisor")
    if not owner or config.get("admission") is not None:
        return False
    try:
        def fields(pid):
            return (proc / str(pid) / "stat").read_text().rsplit(")", 1)[1].split()
        pid = owner["pid"]
        if int(fields(pid)[19]) != owner["start"] or fields(pid)[0] == "Z":
            return False
        args = (proc / str(pid) / "cmdline").read_bytes().decode().strip("\0").split("\0")
        for option, value in (("--run-dir", owner["run_dir"]), ("--workspace", owner["workspace"])):
            if option + "=" + value not in args and not any(a == option and b == value for a, b in zip(args, args[1:])):
                return False
        current, seen = os.getpid(), set()
        while current != pid:
            if current <= 1 or current in seen:
                return False
            seen.add(current)
            current = int(fields(current)[1])
        for descriptor in config["scope_leases"]:
            stat = (proc / str(pid) / "fd" / str(descriptor["fd"])).stat()
            if (stat.st_dev, stat.st_ino) != (descriptor["device"], descriptor["inode"]):
                return False
        return int(fields(pid)[19]) == owner["start"]
    except (OSError, ValueError, KeyError, IndexError, UnicodeError):
        return False


def process_start(pid: int) -> int:
    return int(Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[19])


def detach_compiler_outputs(args: list[str], workspace: Path) -> None:
    """Direct wrapped Lean calls obey the same unlink-before-write rule as Lake."""
    outputs = []
    flags = {"-o", "--o", "-i", "--i", "-c", "--c", "-b", "--bc"}
    for index, arg in enumerate(args):
        flag, separator, value = arg.partition("=")
        if flag not in flags:
            continue
        if not separator:
            if index + 1 == len(args):
                continue
            value = args[index + 1]
        path = Path(os.path.abspath(value))
        if not path.is_relative_to(workspace):
            continue
        outputs.append(path)
        if flag in {"-o", "--o"}:
            outputs.extend([Path(str(path) + ".server"), Path(str(path) + ".private"),
                            path.with_suffix(".ir"), path.with_suffix(".ir.sig")])
    for path in outputs:
        if path.is_symlink():
            path.unlink()
        elif path.is_file() and (path.stat().st_nlink > 1 or not path.stat().st_mode & 0o222):
            path.unlink()


def compiler_main(config_path: Path, args: list[str]) -> int:
    config = json.loads(config_path.read_text())
    real = config["lean"]
    if len(args) == 1 and args[0] in METADATA:
        os.execv(real, [real, *args])
    events = Path(config["events"])
    if config.get("forbid_compilation"):
        event(events, "rejected", reason="no-source-compilation policy", args=args)
        raise ValueError("no-source-compilation policy refused a compiler frontend")
    slots = Path(config["slots"])
    args = compiler_args(args, config["threads"], config["heap_mib"])
    event(events, "waiting", args=args)
    lock = None
    while lock is None:
        for index in range(config["jobs"]):
            candidate = (slots / str(index)).open("a")
            try:
                fcntl.flock(candidate, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                candidate.close()
                continue
            lock = candidate
            break
        if lock is None:
            time.sleep(0.05)
    child, leases = None, []
    elastic_lease = None
    try:
        inherited_scope = []
        for descriptor in config.get("scope_leases", []):
            try:
                stat = os.fstat(descriptor["fd"])
                valid = (stat.st_dev, stat.st_ino) == (descriptor["device"], descriptor["inode"])
            except OSError:
                valid = False
            if valid:
                inherited_scope.append(descriptor["fd"])
        scope_mode = "inherited"
        if len(inherited_scope) != len(config.get("scope_leases", [])):
            if not supervisor_holds_scope(config):
                raise ValueError("scope lease descriptor was not inherited intact and live supervisor ownership is unconfirmed")
            scope_mode = "supervisor-only"
        admission = config.get("admission")
        elastic = config.get("elastic")
        if elastic:
            controller = elastic_component().ElasticPool(elastic["pool"], elastic["limits"], Path(elastic["run_dir"]))
            elastic_lease = controller.acquire("compiler", config["heap_mib"] + FRONTEND_OVERHEAD_MIB,
                                               threads=config["threads"],
                                               oversubscription=elastic.get("oversubscription", False))
            leases.append(elastic_lease)
        elif admission:
            while True:
                tokens = try_admit(admission["pool"], admission["request"])
                if tokens is not None:
                    leases = tokens
                    break
                time.sleep(0.1)
        inherited = [lock.fileno(), *(lease.fileno() for lease in leases), *inherited_scope]
        workspace = Path((config.get("scope_supervisor") or {}).get("workspace", os.getcwd())).resolve()
        detach_compiler_outputs(args, workspace)
        child = subprocess.Popen([real, *args], pass_fds=tuple(inherited))
        if elastic_lease is not None:
            elastic_lease.started(child.pid)
        event(events, "started", compiler_pid=child.pid, slot=index, args=args, cwd=os.getcwd(),
              admission={"mode": "elastic"} if elastic else admission.get("request") if admission else None,
              scope_lease_mode=scope_mode)
        code = child.wait()
        event(events, "finished", compiler_pid=child.pid, slot=index, exit_code=code)
        return code if code >= 0 else 128 - code
    finally:
        if child is not None and child.poll() is None:
            child.terminate()
            try:
                child.wait(timeout=2)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
        close_leases(leases)
        lock.close()


def make_overlay(run_dir: Path, lean: Path, jobs: int, threads: int, heap: int, *,
                 admission: dict | None = None, scope_fds: tuple[int, ...] = (),
                 forbid_compilation: bool = False, scope_supervisor: dict | None = None,
                 elastic: dict | None = None) -> Path:
    overlay = run_dir / "toolchain"
    overlay.mkdir()
    (overlay / "bin").mkdir()
    sysroot = lean.parent.parent
    for item in sysroot.iterdir():
        if item.name != "bin":
            (overlay / item.name).symlink_to(item, target_is_directory=item.is_dir())
    for item in (sysroot / "bin").iterdir():
        if item.name != "lean":
            (overlay / "bin" / item.name).symlink_to(item)
    slots = run_dir / "slots"
    slots.mkdir()
    events = run_dir / "compiler-events.jsonl"
    events.touch(mode=0o600)
    config = run_dir / "compiler-config.json"
    scope_leases = [{"fd": fd, "device": os.fstat(fd).st_dev, "inode": os.fstat(fd).st_ino}
                    for fd in scope_fds]
    config.write_text(json.dumps({"lean": str(lean), "jobs": jobs, "threads": threads,
                                  "heap_mib": heap, "slots": str(slots), "events": str(events),
                                  "admission": admission, "scope_fds": list(scope_fds),
                                  "scope_leases": scope_leases,
                                  "scope_supervisor": scope_supervisor,
                                  "elastic": elastic,
                                  "forbid_compilation": forbid_compilation}))
    command = [sys.executable, str(Path(__file__).resolve()), "__compiler__", str(config)]
    wrapper = overlay / "bin/lean"
    wrapper.write_text("#!/bin/sh\nexec " + shlex.join(command) + ' "$@"\n')
    wrapper.chmod(0o700)
    return overlay


def managed_environment(overlay: Path, lake: Path, jobs: int, threads: int,
                        heap: int, rss: int, path: str, *,
                        source_manifest: Path | None = None,
                        expected_source: str | None = None) -> dict[str, str]:
    """Pass the admitted profile to nested guards without replacing its compiler."""
    lean = str(overlay / "bin/lean")
    profile = {"schema_version": 1, "jobs": jobs, "threads": threads,
               "lean_memory_mib": heap, "rss_limit_mib": rss, "lean": lean}
    env = {"LEAN_SYSROOT": str(overlay), "LAKE_OVERRIDE_LEAN": "1", "LEAN_NUM_THREADS": str(jobs),
           "LEAN": lean, "LAKE": str(lake), "PATH": str(overlay / "bin") + os.pathsep + path,
           "R5_LEAN_REMOTE_PROFILE": json.dumps(profile, sort_keys=True)}
    if source_manifest is not None or expected_source is not None:
        if source_manifest is None or expected_source is None or re.fullmatch(r"[0-9a-f]{64}", expected_source) is None:
            raise ValueError("frozen native execution needs its manifest and exact expected source digest")
        env.update(LEAN_CI_SOURCE_MANIFEST=str(source_manifest), LEAN_CI_EXPECTED_SOURCE=expected_source)
    return env


def process_table(proc: Path = Path("/proc")) -> dict[int, dict]:
    result = {}
    for directory in proc.iterdir():
        if not directory.name.isdecimal():
            continue
        try:
            text = (directory / "stat").read_text()
            fields = text.rsplit(")", 1)[1].split()
            result[int(directory.name)] = {"ppid": int(fields[1]), "pgrp": int(fields[2]),
                                          "state": fields[0], "start": int(fields[19]),
                                          "rss": max(0, int(fields[21])) * os.sysconf("SC_PAGE_SIZE"),
                                          "cpu_ticks": int(fields[11]) + int(fields[12])}
        except (FileNotFoundError, ProcessLookupError):
            continue
    return result


def owned_processes(table: dict[int, dict], pgid: int, owner: int,
                    known: dict[int, int]) -> dict[int, dict]:
    owned = {pid: data for pid, data in table.items()
             if pid != owner and (data["pgrp"] == pgid or data["ppid"] == owner
                                  or known.get(pid) == data["start"])}
    while True:
        new = {pid: data for pid, data in table.items()
               if pid != owner and data["ppid"] in owned and pid not in owned}
        if not new:
            break
        owned.update(new)
    known.update({pid: data["start"] for pid, data in owned.items()})
    return owned


def reap_adopted(pids: dict[int, dict], main_pid: int) -> set[int]:
    reaped = set()
    for pid in pids:
        if pid == main_pid:
            continue
        try:
            result, _ = os.waitpid(pid, os.WNOHANG)
            if result:
                reaped.add(result)
        except ChildProcessError:
            pass
    return reaped


def send_owned(pgid: int, owned: dict[int, dict], signum: int) -> None:
    try:
        os.killpg(pgid, signum)
    except ProcessLookupError:
        pass
    # Also cover owned descendants that deliberately created another group/session.
    for pid, previous in owned.items():
        current = process_table().get(pid)
        if current and current["start"] == previous["start"] and current["pgrp"] != pgid:
            try:
                os.kill(pid, signum)
            except ProcessLookupError:
                pass


def monitor(child: subprocess.Popen, rss_limit: int, cancelled: list[int],
            interval: float = 0.2, grace: float = 5.0, pressure_check=None) -> dict:
    owner, pgid = os.getpid(), child.pid
    known, ticks = {}, {}
    peak, reason, terminating, kill_sent = 0, None, None, False
    started = time.monotonic()
    while True:
        try:
            table = process_table()
        except (OSError, ValueError) as exc:
            # Missing observations cannot certify closure. Keep the global lock,
            # stop the still-owned leader's group, and retry inspection.
            reason = reason or f"process inspection failed: {exc}"
            if child.poll() is None:
                try:
                    os.killpg(pgid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            time.sleep(interval)
            continue
        owned = owned_processes(table, pgid, owner, known)
        for pid in reap_adopted(owned, child.pid):
            owned.pop(pid, None)
        rss = sum(data["rss"] for data in owned.values())
        peak = max(peak, rss)
        for pid, data in owned.items():
            ticks[(pid, data["start"])] = data["cpu_ticks"]
        code = child.poll()
        if code is not None:
            owned.pop(child.pid, None)
        if reason is None:
            if cancelled:
                reason = f"signal {cancelled[0]}"
            elif rss > rss_limit:
                reason = "aggregate RSS cutoff exceeded"
            elif code is not None and owned:
                reason = "command exited with surviving descendants"
            elif pressure_check is not None and (code is None or owned):
                try:
                    reason = pressure_check()
                except (OSError, ValueError) as exc:
                    reason = f"elastic resource inspection failed: {exc}"
        if reason is not None and terminating is None:
            terminating = time.monotonic()
            send_owned(pgid, owned, signal.SIGTERM)
        stop_grace = min(grace, 0.2) if reason and reason.startswith("elastic ") else grace
        if terminating is not None and time.monotonic() - terminating >= stop_grace:
            send_owned(pgid, owned, signal.SIGKILL)
            kill_sent = True
        if code is not None and not owned:
            return {"command_exit_code": code, "failure_reason": reason,
                    "group_closed": True, "peak_rss_bytes": peak,
                    "sampled_process_cpu_seconds": sum(ticks.values()) / os.sysconf("SC_CLK_TCK"),
                    "elapsed_seconds": time.monotonic() - started,
                    "forced_kill": kill_sent}
        # Fail closed: retain the global lock until owned processes really disappear.
        time.sleep(interval)


def capture(argv: list[str], cwd: Path, env: dict) -> str:
    result = subprocess.run(argv, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, timeout=30)
    if result.returncode:
        raise ValueError(f"command failed ({result.returncode}): {shlex.join(argv)}: {result.stderr.strip()}")
    return result.stdout.strip()


def cpu_stat(directory: str) -> dict:
    return {line.split()[0]: int(line.split()[1])
            for line in (Path(directory) / "cpu.stat").read_text().splitlines()}


def memory_events(directory: str) -> dict:
    path = Path(directory) / "memory.events"
    return {line.split()[0]: int(line.split()[1]) for line in path.read_text().splitlines()} if path.is_file() else {}


def compiler_summary(events: Path) -> dict:
    active, peak, count, exits = set(), 0, 0, []
    incomplete = 0
    scope_modes = {}
    with events.open() as stream:
        for line in stream:
            try:
                data = json.loads(line)
            except ValueError:
                incomplete += 1
                continue
            if data["event"] == "started":
                count += 1
                active.add(data["wrapper_pid"])
                peak = max(peak, len(active))
                mode = data.get("scope_lease_mode", "unspecified")
                scope_modes[mode] = scope_modes.get(mode, 0) + 1
            elif data["event"] == "finished":
                active.discard(data["wrapper_pid"])
                exits.append(data["exit_code"])
    return {"compiler_invocations": count, "compiler_succeeded": exits.count(0),
            "compiler_failed": sum(code != 0 for code in exits), "peak_compiler_concurrency": peak,
            "compiler_exit_codes": exits, "unfinished_compiler_records": sorted(active),
            "incomplete_compiler_events": incomplete,
            "compiler_scope_lease_modes": scope_modes,
            "concurrency_basis": "compiler wrapper start/finish intervals, each holding one slot"}


def lake_command(lake: Path, action: str, modules: list[str]) -> list[str]:
    if action == "build":
        return [str(lake), "--rehash", "build", *modules]
    if action == "lint":
        return [str(lake), "--rehash", "lint", "--builtin-only", *modules]
    if action == "cache":
        return [str(lake), "exe", "cache", "get", *modules]
    if action == "plan":
        return [str(lake), "--no-build", "--rehash", "--verbose", "build", *("+" + module for module in modules)]
    raise ValueError(f"unsupported action: {action}")


def owned_phase_command(lake: Path, argv: list[str], forbid: bool) -> list[str]:
    if not argv:
        raise ValueError("phase requires --command followed by executable argv")
    executable = str(lake) if argv[0] == "lake" else shutil.which(argv[0])
    if executable is None:
        raise ValueError("phase executable could not be resolved")
    executable = str(Path(executable).resolve())
    if Path(executable).name in {"sh", "bash", "dash", "zsh", "fish", "cmd", "powershell"}:
        raise ValueError("phase executes argv directly; shell commands are unsupported")
    if forbid:
        options = argv[1:]
        forbidden = ("--dir", "--file", "--packages", "--package", "--reconfigure", "--update")
        if any(value.split("=", 1)[0] in forbidden or value.startswith(("-K", "-R", "-d", "-f"))
               for value in options):
            raise ValueError("no-source phase cannot override or re-elaborate configuration")
        verb = next((i for i, value in enumerate(options) if not value.startswith("-")), None)
        command = options[verb:] if verb is not None else []
        allowed = (command and command[0] == "build" and "--no-build" in options[:verb]) or \
                  (command[:2] in (["cache", "stage"], ["cache", "unstage"])) or \
                  (command and command[0] == "pack")
        if Path(executable) != lake.resolve() or not allowed:
            raise ValueError("no-source phase supports pinned Lake --no-build build, cache stage/unstage, or pack")
    return [executable, *argv[1:]]


# Pinned 4.34.1 source applicability: these whole files import Lake only and
# declare these unconditional requires in order. Unknown Lean configs fail closed.
# Lake/Load/Resolve.lean:185-224,584-626; Lake/Load/Lean/Elab.lean:161-298.
LEAN_CONFIG_ADAPTERS = {
    "274e720ccc7dbabeb9fbf362290dc7e5ed2c5175fbade0ef20cc19b1331affaf":
        ("mathlib", ["batteries", "Qq", "aesop", "proofwidgets", "importGraph", "LeanSearchClient", "plausible"],
         "5fae05c6298a8b59"),
    "0a319fffbf511dab4c3307dc105f8e8fdb4f6160020995cef5f442061cc0abca":
        ("proofwidgets", [], "a4f8a6ba6807ecfe"),
}
CONFIG_ADAPTER_LEAN_HASH = "5045d0056413266e57c625dcd7c365b10e377c52"
PROOFWIDGETS_CONFIG_OPTIONS = {"errorOnBuild":
    "ProofWidgets failed to reuse pre-built JS code. Please report this issue on the Lean Zulip."}


def static_toml_requires(path: Path) -> tuple[str, list[str]]:
    """Read a conservative literal subset, including on Python 3.10 (no tomllib)."""
    name, requires, section, dependency = None, [], "", None
    for raw in path.read_text().splitlines():
        if '\"\"\"' in raw or "'" * 3 in raw:
            raise ValueError("multiline TOML strings are unsupported by the readiness adapter")
        quote, escaped, clean = None, False, []
        for char in raw:
            if quote:
                clean.append(char)
                if escaped: escaped = False
                elif char == "\\" and quote == '\"': escaped = True
                elif char == quote: quote = None
            elif char == "#": break
            else:
                clean.append(char)
                if char in ("'", '\"'): quote = char
        if quote:
            raise ValueError("unverified TOML string syntax")
        line = "".join(clean).strip()
        if not line:
            continue
        if line.startswith("["):
            if any(char in line for char in ("'", '\"')):
                raise ValueError("quoted TOML tables are unsupported by the readiness adapter")
            if dependency is not None:
                if not dependency: raise ValueError("require entry is missing a literal name")
                requires.append(dependency)
                dependency = None
            section = re.sub(r"\s", "", line)
            if section == "[[require]]": dependency = ""
            elif section.startswith(("[require", "[[require")):
                raise ValueError("nested or non-array require configuration is unsupported")
            continue
        if "=" not in line:
            continue
        key, value = (part.strip() for part in line.split("=", 1))
        if any(char in key for char in ("'", '\"')):
            raise ValueError("quoted TOML keys are unsupported by the readiness adapter")
        if not section and (key == "require" or key.startswith("require.")):
            raise ValueError("inline require configuration is unsupported")
        if section == "[[require]]" and (key in ("options", "configFile") or key.startswith("options.")):
            raise ValueError("dependency configuration overrides are unsupported")
        if not section and key == "lakeDir" and value not in ('".lake"', "'.lake'"):
            raise ValueError("nondefault lakeDir is unsupported by the readiness adapter")
        if key != "name" or section not in ("", "[[require]]"):
            continue
        match = re.fullmatch(r"[\"']([A-Za-z_][A-Za-z0-9_'-]*)[\"']", value)
        if not match:
            raise ValueError("package names must be simple literal TOML strings")
        if not section:
            if name is not None: raise ValueError("duplicate package name")
            name = match[1]
        else:
            if dependency: raise ValueError("duplicate require name")
            dependency = match[1]
    if dependency is not None:
        if not dependency: raise ValueError("require entry is missing a literal name")
        requires.append(dependency)
    if name is None:
        raise ValueError("package name is missing from TOML configuration")
    return name, requires


def no_source_configuration(workspace: Path, pins: dict | None = None) -> dict:
    """Check the pinned native warm-load predicate for a limited, explicit family."""
    issues, records, queue, seen = [], [], [(workspace, None, "lakefile")], set()
    pins = pins or {}
    try:
        if (workspace / ".lake/package-overrides.json").exists():
            raise ValueError("workspace package-overrides are unsupported by readiness")
        manifest = json.loads((workspace / "lake-manifest.json").read_text())
        entries = {}
        for entry in manifest.get("packages", []):
            encoded = entry.get("name")
            match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_']*)|«([A-Za-z_][A-Za-z0-9_'-]*)»", encoded or "")
            if match is None:
                raise ValueError("manifest package name is outside the supported Lean.Name JSON subset")
            name = match[1] or match[2]
            if name in entries:
                raise ValueError("manifest dependency names are missing or duplicated")
            entries[name] = entry
        packages_dir = workspace / (manifest.get("packagesDir") or ".lake/packages")
        platform = re.search(r"Lean \(version [^,]+,\s*([^,]+),", pins.get("lean_version", ""))
        platform = platform[1].strip() if platform else None
        for idx, (package, assigned, config_name) in enumerate(queue):
            record = {"idx": idx, "assigned_name": assigned or "[anonymous]", "directory": str(package)}
            records.append(record)
            try:
                if config_name not in ("lakefile", "lakefile.lean", "lakefile.toml"):
                    raise ValueError("custom dependency configuration paths are unsupported")
                config = package / config_name
                if config.suffix == "":
                    config = next((package / (config_name + suffix) for suffix in (".lean", ".toml")
                                   if (package / (config_name + suffix)).is_file()), config)
                if not config.is_file():
                    raise ValueError("package configuration is missing")
                digest = sha256(config)
                record.update(config=str(config), sha256=digest)
                if config.suffix == ".toml":
                    declared, requires = static_toml_requires(config)
                    record["readiness"] = "static_toml"
                else:
                    adapter = LEAN_CONFIG_ADAPTERS.get(digest)
                    if adapter is None or pins.get("lean_githash") != CONFIG_ADAPTER_LEAN_HASH or platform is None:
                        raise ValueError("Lean configuration source/toolchain is outside the verified adapter family")
                    declared, requires, config_hash = adapter
                    if assigned is not None and assigned != declared:
                        raise ValueError("verified Lean config is assigned an unsupported package name")
                    olean = workspace / ".lake/config" / str(idx) / (config.stem + ".olean")
                    trace_file = olean.with_suffix(".olean.trace")
                    if not olean.is_file() or not trace_file.is_file():
                        raise ValueError("prepared Lean configuration olean/trace is missing")
                    trace = json.loads(trace_file.read_text())
                    expected = dict(idx=idx, name=assigned or "[anonymous]", configHash=config_hash,
                                    leanHash=pins["lean_githash"], platform=platform)
                    if any(type(trace.get(key)) is not type(value) or trace.get(key) != value
                           for key, value in expected.items()):
                        raise ValueError("Lean configuration trace differs from the native warm-load predicate")
                    options = trace.get("options")
                    if options != {} and not (declared == "proofwidgets" and options == PROOFWIDGETS_CONFIG_OPTIONS):
                        raise ValueError("Lean configuration options are outside the verified adapter family")
                    record.update(readiness="verified_lean_olean", trace=str(trace_file),
                                  trace_sha256=sha256(trace_file), trace_options=options)
                seen.add(assigned or declared)
                for dependency in reversed(requires):
                    if dependency in seen:
                        continue
                    seen.add(dependency)
                    entry = entries.get(dependency)
                    if entry is None:
                        raise ValueError("required package is missing from the locked root manifest: " + dependency)
                    if entry.get("type") == "path" and isinstance(entry.get("dir"), str):
                        target = workspace / entry["dir"]
                    elif entry.get("type") == "git" and re.fullmatch(r"[0-9a-f]{40,64}", entry.get("rev", "")):
                        target = packages_dir / dependency
                        head = subprocess.run(["git", "-C", str(target), "rev-parse", "HEAD"],
                            capture_output=True, text=True, timeout=10)
                        if head.returncode or head.stdout.strip() != entry["rev"]:
                            raise ValueError("dependency is not already at the locked Git revision: " + dependency)
                        if entry.get("subDir"):
                            target /= entry["subDir"]
                    else:
                        raise ValueError("dependency location/revision is unverified: " + dependency)
                    queue.append((target.resolve(), dependency, entry.get("configFile") or "lakefile"))
            except (OSError, ValueError, TypeError, subprocess.TimeoutExpired) as exc:
                issues.append({"path": record.get("config", str(package)), "reason": str(exc)[:350]})
    except (OSError, ValueError, TypeError) as exc:
        issues.append({"path": str(workspace), "reason": str(exc)[:350]})
    return {"supported": not issues, "configuration_count": len(records),
            "issue_count": len(issues), "issues": issues[:12], "packages": records[:32],
            "packages_truncated": len(records) > 32,
            "boundary": "static TOML plus SHA-guarded Lean 4.34.1 Mathlib/ProofWidgets adapters; ordinary stable olean trust"}


def cache_environment(base: Path) -> dict[str, str]:
    return {"ELAN_HOME": str(base / "elan"), "XDG_CACHE_HOME": str(base / "cache"),
            "LAKE_CACHE_DIR": str(base / "cache/native"), "LAKE_ARTIFACT_CACHE": "true"}


def log_diagnostics(path: Path) -> dict:
    if not path.is_file():
        return {"categories": {}, "first": [], "observed_missing_count": 0,
                "observed_missing_prefixes": {}, "observed_missing_shortlist": []}
    with path.open(errors="replace") as stream:
        return _log_diagnostics(stream)


def _log_diagnostics(stream) -> dict:
    counts, examples, missing = {}, {}, set()
    caption = None
    for raw in stream:
        line = re.sub(r"\x1b\[[0-9;]*m", "", raw).strip()
        match = re.search(r"\]\s+(?:Building|Running|Fetching|Replaying)\s+(\S+)", line)
        if match:
            caption = match[1]
        low = line.lower()
        if "out-of-date and needs to be rebuilt" in low:
            missing.add(caption or "<unresolved-target>")
        if "error:" not in low and "warning:" not in low and "no-source-compilation policy" not in low:
            continue
        if "no-source-compilation policy" in low: kind = "compilation_refused"
        elif any(x in low for x in ("excessive memory", "out of memory", "memory exhausted")): kind = "memory_budget"
        elif "heartbeats" in low: kind = "heartbeat_budget"
        elif "recursion depth" in low: kind = "recursion_budget"
        elif "unexpected token" in low: kind = "source_syntax"
        elif "unknown identifier" in low or "unknown constant" in low or "unknown namespace" in low: kind = "source_name"
        elif "sorryax" in low: kind = "unsupported_assumption_diagnostic"
        elif "warning:" in low: kind = "lint_warning"
        elif any(x in low for x in ("type mismatch", "unsolved goals", "failed to synthesize", "tactic")): kind = "source_elaboration"
        else: kind = "other_error"
        counts[kind] = counts.get(kind, 0) + 1
        examples.setdefault(kind, line[:350])
    prefixes = {}
    for target in missing:
        prefix = target.split(".", 1)[0]
        prefixes[prefix] = prefixes.get(prefix, 0) + 1
    order = ("compilation_refused", "memory_budget", "source_syntax", "source_name", "heartbeat_budget",
             "recursion_budget", "source_elaboration", "unsupported_assumption_diagnostic", "other_error", "lint_warning")
    return {"categories": counts, "first": [examples[kind] for kind in order if kind in examples][:5],
            "observed_missing_count": len(missing), "observed_missing_prefixes": dict(sorted(prefixes.items())[:12]),
            "observed_missing_prefixes_truncated": len(prefixes) > 12,
            "observed_missing_shortlist": sorted(missing)[:12]}


def classify_outcome(receipt: dict, diagnostics: dict) -> str:
    if receipt.get("cancelled_signal"):
        return "cancelled"
    if receipt.get("failure_class"):
        return receipt["failure_class"]
    if (receipt.get("failure_reason") or "").startswith("elastic "):
        return "resource_pressure"
    if (receipt.get("failure_reason") or "").startswith("disk reserve"):
        return "disk_pressure"
    if receipt.get("failure_reason", "") and "RSS cutoff" in receipt["failure_reason"]:
        return "rss_guard"
    if receipt.get("input_drift"):
        return "input_drift"
    if receipt.get("command_exit_code") is not None and receipt["command_exit_code"] < 0:
        if receipt.get("cgroup_memory_events_delta", {}).get("oom_kill", 0):
            return "signal_termination_with_cgroup_oom_evidence"
        return "signal_termination"
    if receipt.get("exit_code") == 0:
        if receipt["action"] == "plan": return "cache_ready"
        if receipt["action"] == "phase": return "owned_phase_completed"
        if receipt["action"] == "lint": return "lint_passed"
        if receipt["action"] == "cache": return "cache_fetch_completed"
        return "native_build_completed" if receipt.get("compiler_invocations") else "cached_build_accepted"
    if receipt.get("command_exit_code") == 3 and receipt.get("forbid_compilation"):
        return "cache_missing"
    categories = diagnostics["categories"]
    for kind in ("compilation_refused", "memory_budget", "source_syntax", "source_name", "heartbeat_budget",
                 "recursion_budget", "source_elaboration", "unsupported_assumption_diagnostic"):
        if categories.get(kind):
            return kind
    if receipt["action"] == "lint" and categories.get("lint_warning"):
        return "lint_diagnostics"
    return "execution_failure"


def run_summary(receipt: dict) -> dict:
    run_dir = Path(receipt["run_dir"])
    diagnostics = log_diagnostics(run_dir / "build.log")
    receipt["diagnostics"] = diagnostics
    outcome = classify_outcome(receipt, diagnostics)
    receipt["outcome"] = outcome
    receipt["compiler_observation"] = "wrapper-events-only"
    if receipt["action"] == "plan":
        receipt.setdefault("plan", {}).update(ready=receipt.get("exit_code") == 0,
            native_exit_code=receipt.get("command_exit_code"), missing_observation_complete=receipt.get("exit_code") == 0,
            **{k: v for k, v in diagnostics.items() if k.startswith("observed_missing")})
    return {"status": receipt["status"], "action": receipt["action"], "outcome": outcome,
            "run": run_dir.name, "source_basis": receipt.get("source_content_sha256"),
            "expected_source": receipt.get("expected_source"),
            "reason": (receipt.get("failure_reason") or receipt.get("error") or "")[:350],
            "native_exit": receipt.get("command_exit_code"), "exit_code": receipt.get("exit_code"),
            "group_closed": receipt.get("group_closed"), "profile": receipt["profile"],
            "frontend_invocations": receipt.get("compiler_invocations", 0),
            "frontend_succeeded": receipt.get("compiler_succeeded", 0),
            "frontend_failed": receipt.get("compiler_failed", 0),
            "frontend_peak": receipt.get("peak_compiler_concurrency", 0),
            "peak_rss_bytes": receipt.get("peak_rss_bytes"),
            "sampled_process_average_cpu_cores": receipt.get("sampled_process_average_cpu_cores"),
            "admission": {key: receipt.get("admission", {}).get(key) for key in
                          ("mode", "request", "max_frontends_if_alone", "affinity_cpus", "ceilings",
                           "initial_observation", "final_observation", "controller_sha256")},
            "cgroup_memory_events_delta": receipt.get("cgroup_memory_events_delta"),
            "cgroup_memory_attribution": "whole observed cgroup; an OOM event alone does not identify its victim",
            "compiler_observation": receipt["compiler_observation"],
            "compiler_scope_lease_modes": receipt.get("compiler_scope_lease_modes", {}),
            "unwrapped_frontend_count": "unknown" if receipt["action"] == "phase" else None,
            "frontend_observation": "wrapper starts only; arbitrary phase tools may bypass local compiler caps" if
                                    receipt["action"] == "phase" else
                                    "worker-wrapper events, not Lake job totals or retained coverage",
            "wall_seconds": receipt.get("wall_seconds"), "execution_seconds": receipt.get("elapsed_seconds"),
            "first_diagnostics": diagnostics["first"],
            "plan": receipt.get("plan"),
            "artifacts": {name: str(run_dir / name) for name in ("receipt.json", "build.log", "compiler-events.jsonl")}}


def write_receipt(path: Path, data: dict) -> None:
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def prune_closed_run_setups(workspace: Path, events: Path) -> dict:
    paths = set()
    for line in events.read_text().splitlines():
        item = json.loads(line)
        if item.get("event") != "started":
            continue
        args = item.get("args", [])
        for index, arg in enumerate(args):
            name = args[index + 1] if arg == "--setup" and index + 1 < len(args) else (
                arg.split("=", 1)[1] if arg.startswith("--setup=") else None)
            if name:
                paths.add(Path(item.get("cwd", str(workspace))) / name)
    return storage_component().prune_setups(workspace, paths)


def run(args: argparse.Namespace) -> int:
    apply_resource_defaults(args)
    if args.action in ("plan", "phase") and args.expected_source is None:
        raise ValueError("plan and owned phase require an exact --expected-source")
    if args.action != "phase" and (args.phase_command or args.forbid_compilation):
        raise ValueError("--command and --forbid-compilation belong to phase; plan is always source-free")
    workspace, run_dir, inputs = validate_inputs(args.base, args.workspace, args.run_dir,
                                               args.action, args.modules,
                                               allow_library_roots=args.allow_library_roots)
    if not sys.platform.startswith("linux"):
        raise ValueError("the worker requires Linux /proc and cgroup v2")
    limits = resource_limits()
    validate_profile(args.jobs, args.threads, args.lean_memory_mib, args.rss_limit_mib, limits,
                     allow_cpu_oversubscription=args.allow_cpu_oversubscription)
    run_dir.mkdir(parents=True, mode=0o700)
    (run_dir / "build.log").touch(mode=0o600)
    (run_dir / "compiler-events.jsonl").touch(mode=0o600)
    started_at = time.monotonic()
    receipt_path = run_dir / "receipt.json"
    receipt = {"schema_version": 1, "started_at": now(), "status": "waiting",
               "expected_source": args.expected_source,
               "task_id": getattr(args, "task_id", None), "operation_id": getattr(args, "operation_id", None),
               "workspace": str(workspace), "action": args.action, "modules": args.modules,
               "allow_library_roots": args.allow_library_roots,
               "profile": {"jobs": args.jobs, "threads": args.threads,
                           "allow_cpu_oversubscription": args.allow_cpu_oversubscription,
                           "lean_memory_mib": args.lean_memory_mib, "rss_limit_mib": args.rss_limit_mib},
               "resources": limits, "worker_sha256": sha256(Path(__file__)),
               "run_dir": str(run_dir), "group_closed": True}
    forbid = args.action == "plan" or args.forbid_compilation
    receipt.update(forbid_compilation=forbid, phase_label=args.label if args.action == "phase" else None)
    write_receipt(receipt_path, receipt)
    cancelled = []
    previous = {}
    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        previous[signum] = signal.signal(signum, lambda sig, frame: cancelled.append(sig))
    locks = []
    controller = run_lease = None
    child = None
    try:
        base = args.base.resolve()
        receipt.update(waiting_for="idle_elastic_admission_migration")
        write_receipt(receipt_path, receipt)
        pool = prepare_elastic_pool(base, limits, cancelled)
        locks = acquire_run_locks(base, workspace, args.action, cancelled)
        if cancelled:
            raise ValueError("cancelled before starting build")
        storage = storage_component() if (base / "storage/policy.json").is_file() else None
        if storage is not None:
            storage.mark_used(base, workspace)
        source_receipt = workspace.parent / "SOURCE.json"
        source_basis = json.loads(source_receipt.read_text()) if source_receipt.is_file() else {}
        receipt["source_content_sha256"] = source_basis.get("content_sha256")
        if "workspace" in source_basis and source_basis["workspace"] != str(workspace):
            receipt["failure_class"] = "source_basis_mismatch"
            raise ValueError("SOURCE.json workspace owner differs from the requested workspace")
        if args.expected_source is not None:
            if not source_receipt.is_file():
                raise ValueError("expected-source requires workspace.parent/SOURCE.json")
            actual_source = source_basis.get("content_sha256")
            if actual_source != args.expected_source:
                receipt["failure_class"] = "source_basis_mismatch"
                raise ValueError("workspace source digest differs from --expected-source")
        receipt["expected_source"] = args.expected_source
        if source_receipt.is_file():
            receipt["source_receipt_sha256"] = sha256(source_receipt)
            receipt["source_content_sha256"] = source_basis.get("content_sha256")
        controller = elastic_component().ElasticPool(pool, limits, run_dir)
        admission = {"mode": "elastic", "max_frontends_if_alone": args.jobs,
                     "ceilings": receipt["profile"],
                     "controller_sha256": sha256(Path(__file__).with_name(ELASTIC_MODULE))}
        receipt["admission"] = admission
        receipt["resource_accounting"] = {
            "global": "sampled cgroup memory/CPU, startup and growth credits; no peak-envelope reservation",
            "run": "frontend/job/thread ceilings, sampled owned-tree RSS cutoff, own-tree pressure retreat",
            "isolation": "cooperative sampled admission; no per-run kernel memory isolation or OOM guarantee",
        }
        receipt["locks"] = {"legacy_shared_gate": str(base / "build.lock"),
                            "workspace_exclusive": str(workspace_lock_path(base, workspace)),
                            "cache_fetch_exclusive": str(base / "locks/cache-fetch.lock") if args.action == "cache" else None}
        env = dict(os.environ)
        for name in ("ELAN_TOOLCHAIN", "LEAN", "LEAN_SYSROOT", "LEAN_GITHASH", "LAKE_HOME",
                     "LAKE_OVERRIDE_LEAN", "LEAN_AR", "LEAN_CC", "LAKE"):
            env.pop(name, None)
        env.update(cache_environment(base))
        elan = base / "elan/bin/elan"
        elan_command = str(elan) if elan.is_file() else shutil.which("elan")
        if not elan_command:
            raise ValueError("cannot find the Elan launcher")
        lean = Path(capture([elan_command, "which", "lean"], workspace, env)).resolve(strict=True)
        within(lean, base / "elan/toolchains")
        lake = lean.parent / "lake"
        if not lake.is_file():
            raise ValueError("pinned Lake must be adjacent to the pinned Lean compiler")
        githash = capture([str(lean), "--githash"], workspace, env)
        if not githash or not re.fullmatch(r"[0-9a-fA-F]{40,64}", githash):
            raise ValueError("pinned Lean returned an invalid githash")
        receipt["pins"] = {"lean": str(lean), "lake": str(lake), "lean_githash": githash,
                           "lean_version": capture([str(lean), "--version"], workspace, env),
                           "lake_version": capture([str(lake), "--version"], workspace, env),
                           "lean_sha256": sha256(lean), "lake_sha256": sha256(lake)}
        receipt["input_sha256"] = {str(path.relative_to(workspace)): sha256(path) for path in inputs}
        try:
            receipt["git_head"] = capture(["git", "rev-parse", "HEAD"], workspace, env)
            receipt["git_dirty_tracked"] = capture(["git", "status", "--porcelain", "--untracked-files=no"], workspace, env)
        except ValueError:
            receipt["git_head"] = None
        receipt["cache_provenance"] = {"environment": {key: env[key] for key in
            ("LAKE_CACHE_DIR", "LAKE_ARTIFACT_CACHE", "XDG_CACHE_HOME")},
            "configuration_sha256": {name: digest for name, digest in receipt["input_sha256"].items()
                                     if name in ("lakefile.toml", "lakefile.lean", "lake-manifest.json")},
            "lookup": "native Lake traces/artifact cache; no per-dependency prior-hit claim"}
        command = owned_phase_command(lake, args.phase_command or [], forbid) if args.action == "phase" else \
                  lake_command(lake, args.action, args.modules)
        if args.action == "phase":
            receipt["phase_executable_sha256"] = sha256(Path(command[0]))
        if forbid:
            boundary = no_source_configuration(workspace, receipt["pins"])
            receipt["configuration_boundary"] = boundary
            if not boundary["supported"]:
                receipt.update(status="failed", exit_code=3, failure_class="configuration_unverified",
                               failure_reason="no-source policy cannot verify all configuration caches")
                (run_dir / "build.log").write_text(json.dumps(boundary, indent=2) + "\n")
                return 3
        receipt.update(waiting_for="elastic_resource_headroom")
        write_receipt(receipt_path, receipt)
        run_lease = controller.acquire("run", args.rss_limit_mib,
                                       threads=args.jobs * args.threads, cancelled=cancelled)
        locks.append(run_lease)
        admission["initial_observation"] = controller.snapshot()
        scope_fds = tuple(lease.fileno() for lease in locks)
        supervisor = {"pid": os.getpid(), "start": process_start(os.getpid()),
                      "run_dir": str(run_dir), "workspace": str(workspace)}
        overlay = make_overlay(run_dir, lean, args.jobs, args.threads, args.lean_memory_mib,
                               scope_fds=scope_fds, forbid_compilation=forbid, scope_supervisor=supervisor,
                               elastic={"pool": pool, "limits": limits, "run_dir": str(run_dir),
                                        "oversubscription": args.allow_cpu_oversubscription})
        receipt["compiler_scope_policy"] = "workspace descriptors or verified live supervisor; each compiler inherits its elastic claim"
        env.update(managed_environment(overlay, lake, args.jobs, args.threads,
                                       args.lean_memory_mib, args.rss_limit_mib, env.get("PATH", ""),
                                       source_manifest=source_receipt if args.action == "phase" else None,
                                       expected_source=args.expected_source if args.action == "phase" else None))
        # Become a subreaper before launch so double-forked descendants remain owned.
        if ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), "cannot enable child subreaper")
        receipt.update(command=command, actor_executable=command[0], status="running", lock_acquired_at=now(),
                       cgroup_cpu_before=cpu_stat(limits["cgroup"]),
                       cgroup_memory_events_before=memory_events(limits["cgroup"]), waiting_for=None,
                       environment={key: env[key] for key in ("ELAN_HOME", "XDG_CACHE_HOME", "LAKE_CACHE_DIR", "LAKE_ARTIFACT_CACHE",
                                                            "LEAN_SYSROOT", "LAKE_OVERRIDE_LEAN", "LEAN_NUM_THREADS",
                                                            "R5_LEAN_REMOTE_PROFILE")})
        write_receipt(receipt_path, receipt)
        with (run_dir / "build.log").open("wb") as log:
            child = spawn_owned(command, affinity=limits.get("affinity"), cwd=workspace, env=env, stdout=log,
                                     stderr=subprocess.STDOUT, start_new_session=True,
                                     pass_fds=scope_fds)
            run_lease.started(child.pid)
            receipt.update(pgid=child.pid, group_closed=False)
            # For an executable script /proc/exe names its actual interpreter.
            try:
                receipt["actor_executable"] = os.readlink(f"/proc/{child.pid}/exe")
            except FileNotFoundError:
                pass  # A very short completed command may already have exited.
            write_receipt(receipt_path, receipt)
            def pressure_check():
                reason = controller.pressure_victim(run_lease)
                if reason:
                    return reason
                if storage is not None:
                    try:
                        free = shutil.disk_usage(base).free
                        receipt["lowest_disk_free_bytes"] = min(free, receipt.get("lowest_disk_free_bytes", free))
                        if free < storage.policy(base)["low_free_bytes"]:
                            receipt["disk_pressure_observed"] = True
                    except Exception as exc:
                        receipt["storage_observation_error"] = str(exc)
                return None
            receipt.update(monitor(child, args.rss_limit_mib * MIB, cancelled,
                                   pressure_check=pressure_check))
        admission["final_observation"] = controller.snapshot()
        receipt.update(compiler_summary(run_dir / "compiler-events.jsonl"))
        receipt["cgroup_cpu_after"] = cpu_stat(limits["cgroup"])
        receipt["cgroup_memory_events_after"] = memory_events(limits["cgroup"])
        receipt["cgroup_memory_events_delta"] = {key: value - receipt["cgroup_memory_events_before"].get(key, 0)
            for key, value in receipt["cgroup_memory_events_after"].items()}
        usage = receipt["cgroup_cpu_after"].get("usage_usec", 0) - receipt["cgroup_cpu_before"].get("usage_usec", 0)
        receipt["cgroup_cpu_seconds_delta"] = usage / 1_000_000
        receipt["cgroup_average_cpu_cores"] = usage / 1_000_000 / max(receipt["elapsed_seconds"], 0.001)
        receipt["sampled_process_average_cpu_cores"] = receipt["sampled_process_cpu_seconds"] / max(receipt["elapsed_seconds"], 0.001)
        receipt["cgroup_cpu_attribution"] = "whole observed cgroup; may include unrelated activity"
        receipt["input_drift"] = [name for name, digest in receipt["input_sha256"].items()
                                  if not (workspace / name).is_file() or sha256(workspace / name) != digest]
        failed = bool(receipt["failure_reason"] or receipt["command_exit_code"] or receipt["input_drift"])
        receipt["status"] = "failed" if failed else "succeeded"
        code = 128 + cancelled[0] if cancelled else (receipt["command_exit_code"] or (1 if failed else 0))
        code = code if code >= 0 else 128 - code
        receipt["exit_code"] = code
        return code
    except BaseException as exc:
        receipt.update(status="failed", error=str(exc), exit_code=1)
        if child is not None and not receipt.get("group_closed"):
            cancelled.append(signal.SIGTERM)
            receipt.update(monitor(child, args.rss_limit_mib * MIB, cancelled))
        receipt["exit_code"] = 128 + cancelled[0] if cancelled else 1
        return receipt["exit_code"]
    finally:
        receipt["finished_at"] = now()
        receipt["wall_seconds"] = time.monotonic() - started_at
        if locks and receipt.get("group_closed"):
            try:
                receipt["setup_cleanup"] = prune_closed_run_setups(workspace, run_dir / "compiler-events.jsonl")
            except Exception as exc:
                receipt["setup_cleanup_error"] = str(exc)
        if cancelled:
            receipt["cancelled_signal"] = cancelled[0]
        try:
            try:
                receipt["summary"] = run_summary(receipt)
            except (OSError, ValueError, KeyError) as exc:
                receipt["summary"] = {"run": run_dir.name, "status": receipt["status"],
                    "exit_code": receipt.get("exit_code"), "group_closed": receipt.get("group_closed"),
                    "summary_error": str(exc)[:350], "receipt": str(receipt_path)}
            write_receipt(receipt_path, receipt)
        finally:
            # monitor deliberately does not return with surviving owned descendants.
            if locks and (args.base / "storage/policy.json").is_file():
                try:
                    storage_component().mark_used(args.base.resolve(), workspace, finished=True)
                    if receipt.get("group_closed") and getattr(args, "operation_id", None) and getattr(args, "task_id", None):
                        storage_component().finish_operation(args.base.resolve(), workspace, args.task_id, args.operation_id)
                except Exception as exc:
                    print("storage usage update: " + str(exc), file=sys.stderr)
            close_leases(locks)
            for signum, handler in previous.items():
                signal.signal(signum, handler)
        print(json.dumps(receipt["summary"], sort_keys=True))


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv and argv[0] == "__compiler__":
        return compiler_main(Path(argv[1]), argv[2:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--run-dir", type=Path, required=True)
    parser.add_argument("--expected-source", help="expected SOURCE.json content_sha256, checked under lock")
    parser.add_argument("--task-id", help="owning task lease, independent of source-root reuse")
    parser.add_argument("--operation-id", help="invocation lease spanning source transport and queued execution")
    parser.add_argument("--jobs", type=int)
    parser.add_argument("--threads", type=int)
    parser.add_argument("--allow-library-roots", action="store_true",
                        help="allow explicitly named existing local source roots, only for build")
    parser.add_argument("--allow-cpu-oversubscription", action="store_true",
                        help="allow up to twice effective CPUs in frontend jobs, only with --threads 1")
    parser.add_argument("--lean-memory-mib", type=int)
    parser.add_argument("--rss-limit-mib", type=int)
    parser.add_argument("--label", default="owned-phase")
    parser.add_argument("--forbid-compilation", action="store_true")
    parser.add_argument("--command", dest="phase_command", nargs=argparse.REMAINDER)
    parser.add_argument("action", choices=("build", "cache", "lint", "plan", "phase"))
    parser.add_argument("modules", nargs="+")
    args = parser.parse_args(argv)
    try:
        return run(args)
    except (ValueError, OSError, subprocess.TimeoutExpired) as exc:
        print(f"lean remote worker: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
