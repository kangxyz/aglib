"""Synchronize identified Lean inputs and run scoped builds over existing SSH."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shlex
import subprocess
import tarfile
import tempfile
import uuid


PINS = {"lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json"}
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+")
RESOURCE_KEYS = ("jobs", "threads", "lean_memory_mib", "rss_limit_mib")

# This small receiver runs with the remote system Python, without installing r5sys.
# The archive contains regular source files and its explicit ownership manifest.
APPLY_SOURCE = r'''
import fcntl, hashlib, json, os, pathlib, sys, tarfile, tempfile
base, workspace = map(pathlib.Path, sys.argv[1:3])
base, workspace = base.resolve(), workspace.resolve()
if not workspace.is_relative_to(base / 'workspaces') or workspace == base / 'workspaces':
    raise SystemExit('Workspace must be inside base/workspaces')
(base / 'downloads').mkdir(parents=True, exist_ok=True)
def digest(data): return hashlib.sha256(data).hexdigest()
def local(name):
    p = pathlib.PurePosixPath(name)
    if not name or p.is_absolute() or '..' in p.parts or any(x in {'.git', '.lake'} for x in p.parts):
        raise SystemExit('Invalid source member: ' + name)
    target = workspace / name
    if not target.resolve().is_relative_to(workspace):
        raise SystemExit('Source path escapes workspace: ' + name)
    return target
with tempfile.TemporaryFile(dir=base / 'downloads') as stream:
    while True:
        data = sys.stdin.buffer.read(1048576)
        if not data: break
        stream.write(data)
        if stream.tell() > 536870912: raise SystemExit('Source archive too large')
    stream.seek(0)
    with tarfile.open(fileobj=stream, mode='r:gz') as archive:
        members = archive.getmembers()
        if any(not m.isfile() for m in members) or sum(m.size for m in members) > 536870912:
            raise SystemExit('Expected a bounded archive of regular source files')
        names = [m.name for m in members]
        if len(names) != len(set(names)): raise SystemExit('Duplicate source members')
        manifest = json.load(archive.extractfile('.remote-source.json'))
        files = manifest['files']
        if set(names) != set(files) | {'.remote-source.json'}:
            raise SystemExit('Archive and source ownership manifest differ')
        expected = digest(json.dumps(files, sort_keys=True, separators=(',', ':')).encode())
        if expected != manifest['content_sha256']: raise SystemExit('Source identity mismatch')
        data = {}
        for name, checksum in files.items():
            local(name)
            data[name] = archive.extractfile(name).read()
            if digest(data[name]) != checksum: raise SystemExit('Source checksum mismatch: ' + name)
    base.mkdir(parents=True, exist_ok=True)
    locks = base / 'locks'
    locks.mkdir(exist_ok=True)
    owner = digest(str(workspace.parent).encode())
    with (base / 'build.lock').open('a') as legacy, (locks / ('workspace-' + owner + '.lock')).open('a') as lock:
        fcntl.flock(legacy, fcntl.LOCK_SH)
        fcntl.flock(lock, fcntl.LOCK_EX)
        basis = workspace.parent / 'SOURCE.json'
        previous = json.loads(basis.read_text()) if basis.exists() else {}
        if previous.get('workspace') not in (None, str(workspace)):
            raise SystemExit('Source container belongs to another workspace; choose a separate workspace parent')
        manifest['workspace'] = str(workspace)
        for name, checksum in previous.get('files', {}).items():
            target = local(name)
            if target.exists() and digest(target.read_bytes()) != checksum:
                raise SystemExit('Remote source drift; inspect before replacing: ' + name)
        for name, checksum in files.items():
            target = local(name)
            if name not in previous.get('files', {}) and target.exists() and (not target.is_file() or digest(target.read_bytes()) != checksum):
                raise SystemExit('Existing remote path has no synchronized ownership: ' + name)
        for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'lakefile.toml'):
            target = local(name)
            if target.exists() and (name not in data or target.read_bytes() != data[name]):
                raise SystemExit('Build configuration changed; prepare its exact dependencies in a separate workspace: ' + name)
        changed = removed = 0
        workspace.mkdir(parents=True, exist_ok=True)
        def write_basis(value):
            with tempfile.NamedTemporaryFile(mode='w', dir=workspace.parent, delete=False) as out:
                json.dump(value, out, sort_keys=True, indent=2)
                out.write('\n')
                temporary = pathlib.Path(out.name)
            os.replace(temporary, basis)
        # A failed multi-file update must never retain the old admissible digest.
        write_basis(dict(previous, content_sha256=None, sync_incomplete=True))
        for name, value in data.items():
            target = local(name)
            if target.is_file() and digest(target.read_bytes()) == files[name]: continue
            target.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as out:
                out.write(value)
                temporary = pathlib.Path(out.name)
            temporary.chmod(0o644)
            os.replace(temporary, target)
            changed += 1
        for name in previous.get('files', {}).keys() - files.keys():
            target = local(name)
            if target.is_file(): target.unlink(); removed += 1
        write_basis(manifest)
        print(json.dumps({'content_sha256': expected, 'changed_files': changed, 'removed_files': removed,
                          'source_files': len(files), 'git_head': manifest['git_head']}))
'''

STATUS = r'''
import json, os, pathlib, shutil, sys
b, w = map(pathlib.Path, sys.argv[1:3])
def read(p):
    p = pathlib.Path('/sys/fs/cgroup') / p
    return p.read_text().strip() if p.is_file() else None
basis = w.parent / 'SOURCE.json'
print(json.dumps({'affinity_cpus': len(os.sched_getaffinity(0)), 'cpu_max': read('cpu.max'),
 'memory_max': read('memory.max'), 'memory_current': read('memory.current'),
 'disk_free_bytes': shutil.disk_usage(b).free, 'workspace': str(w),
 'source': json.loads(basis.read_text()) if basis.exists() else None}, sort_keys=True))
'''

DEPLOY_WORKER = r'''
import hashlib, os, pathlib, sys, tempfile
base = pathlib.Path(sys.argv[1])
checksum = sys.argv[2]
kind = sys.argv[3] if len(sys.argv) > 3 else 'lean_remote_worker'
if kind not in {'lean_remote_worker', 'lean_remote_elastic', 'lean_remote_storage'}:
    raise SystemExit('Unsupported worker component')
data = sys.stdin.buffer.read()
if hashlib.sha256(data).hexdigest() != checksum:
    raise SystemExit('Worker checksum mismatch')
directory = base / 'bin'
directory.mkdir(parents=True, exist_ok=True)
target = directory / (kind + '-' + checksum + '.py')
with tempfile.NamedTemporaryFile(dir=directory, delete=False) as stream:
    stream.write(data)
    temporary = pathlib.Path(stream.name)
try:
    temporary.chmod(0o755)
    try:
        os.link(temporary, target)
    except FileExistsError:
        if target.is_symlink() or not target.is_file() or hashlib.sha256(target.read_bytes()).hexdigest() != checksum:
            raise SystemExit('Existing versioned worker differs from its identity')
finally:
    temporary.unlink()
print(target)
'''


class RemoteLeanError(ValueError):
    pass


def load_config(path: Path, *, require_source_root: bool = True) -> dict:
    raw = path.read_bytes()
    config = json.loads(raw)
    if re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.@-]*", config["host"]) is None:
        raise RemoteLeanError("host must be an SSH alias or host name, without shell options")
    for key in ("base", "workspace"):
        value = config[key]
        if not re.fullmatch(r"/[A-Za-z0-9_/.-]+", value) or ".." in PurePosixPath(value).parts:
            raise RemoteLeanError(f"{key} must be an absolute remote path without shell characters")
    base, workspace = PurePosixPath(config["base"]), PurePosixPath(config["workspace"])
    if base == PurePosixPath("/") or not workspace.is_relative_to(base / "workspaces") or workspace == base / "workspaces":
        raise RemoteLeanError("workspace must be below base/workspaces")
    config["source_root"] = str(Path(config["source_root"]).expanduser().resolve(strict=require_source_root))
    config["local_logs"] = str(Path(config["local_logs"]).expanduser().resolve())
    config["_config_path"] = str(path.resolve())
    config["_config_sha256"] = hashlib.sha256(raw).hexdigest()
    interpreter = config.get("remote_python", "python3")
    if not isinstance(interpreter, str) or not re.fullmatch(r"(?:/[A-Za-z0-9_./-]+|[A-Za-z][A-Za-z0-9_.-]*)", interpreter):
        raise RemoteLeanError("remote_python must name one interpreter executable")
    return config


def ssh(config: dict, argv: list[str], **kwargs) -> subprocess.CompletedProcess:
    if argv and argv[0] == "python3":
        argv = [config.get("remote_python", "python3"), *argv[1:]]
    return subprocess.run(["ssh", "-o", "BatchMode=yes", config["host"], shlex.join(argv)], **kwargs)


def source_snapshot(root: Path, include: list[str] | None = None) -> tuple[dict, dict[str, bytes]]:
    """Read stable regular inputs once; never transfer .git or native build output."""
    root = root.resolve(strict=True)
    head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    names = subprocess.check_output([
        "git", "-C", str(root), "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "."
    ]).decode().split("\0")
    selected = {name for name in names if name and (name.endswith(".lean") or name in PINS)}
    selected.update(include or [])
    data, stats = {}, {}
    for name in sorted(selected):
        relative = PurePosixPath(name)
        if relative.is_absolute() or ".." in relative.parts or any(part in {".git", ".lake"} for part in relative.parts):
            raise RemoteLeanError(f"invalid source path: {name}")
        path = root / name
        if not path.exists():
            continue  # A tracked deletion is a source change, not a missing input.
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(root):
            raise RemoteLeanError(f"source must be a regular in-root file: {name}")
        before = source_stat(path)
        value = path.read_bytes()
        after = source_stat(path)
        if before != after:
            raise RemoteLeanError(f"source changed while reading: {name}")
        data[name], stats[name] = value, after
    if "lean-toolchain" not in data or "lake-manifest.json" not in data or not {"lakefile.lean", "lakefile.toml"} & data.keys():
        raise RemoteLeanError("select a configured Lean package with committed dependency pins")
    for name, previous in stats.items():
        if source_stat(root / name) != previous:
            raise RemoteLeanError(f"source changed during snapshot: {name}")
    if subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip() != head:
        raise RemoteLeanError("HEAD changed during source snapshot")
    files = {name: hashlib.sha256(value).hexdigest() for name, value in data.items()}
    digest = hashlib.sha256(json.dumps(files, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"content_sha256": digest, "git_head": head, "source_root": str(root), "files": files}, data


def source_stat(path: Path) -> tuple[int, ...]:
    stat = path.stat()
    return stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns


def sync_source(config: dict, include: list[str] | None = None, *, bootstrap=False) -> str:
    manifest, data = source_snapshot(Path(config["source_root"]), include)
    if not bootstrap:
        config["_operation_id"] = uuid.uuid4().hex
        storage_command(config, "use", pins={name: value.decode() for name, value in data.items() if name in PINS})
    print("Synchronizing source inputs; writes wait for this workspace's active build.", file=os.sys.stderr, flush=True)
    with tempfile.TemporaryFile() as stream:
        with gzip.GzipFile(fileobj=stream, mode="wb", mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w|") as archive:
                data = dict(data, **{".remote-source.json": json.dumps(manifest, sort_keys=True).encode()})
                for name, value in sorted(data.items()):
                    member = tarfile.TarInfo(name)
                    member.size, member.mode = len(value), 0o644
                    archive.addfile(member, io.BytesIO(value))
        stream.seek(0)
        try:
            result = ssh(config, ["python3", "-c", APPLY_SOURCE, config["base"], config["workspace"]],
                         stdin=stream, text=True, stdout=subprocess.PIPE, check=True)
        except subprocess.CalledProcessError as exc:
            config["_operation_unconfirmed"] = exc.returncode == 255
            raise
    print(result.stdout.strip(), flush=True)
    observed = json.loads(result.stdout)
    if observed["content_sha256"] != manifest["content_sha256"]:
        raise RemoteLeanError("remote synchronization returned a different source identity")
    return manifest["content_sha256"]


def deploy_worker(config: dict) -> str:
    """Install an immutable worker version without replacing another client's code."""
    source = Path(__file__).with_name("lean_remote_worker.py")
    content = source.read_bytes()
    storage_name = PurePosixPath(deploy_storage(config)).name
    storage_marker = b'STORAGE_MODULE = "lean_remote_storage.py"'
    if content.count(storage_marker) != 1:
        raise RemoteLeanError("worker storage binding changed")
    content = content.replace(storage_marker, ('STORAGE_MODULE = "' + storage_name + '"').encode())
    controller = source.with_name("lean_remote_elastic.py").read_bytes()
    controller_hash = hashlib.sha256(controller).hexdigest()
    controller_name = "lean_remote_elastic-" + controller_hash + ".py"
    result = ssh(config, ["python3", "-c", DEPLOY_WORKER, config["base"], controller_hash, "lean_remote_elastic"],
                 input=controller, check=True, capture_output=True)
    if result.stdout.decode().strip() != config["base"] + "/bin/" + controller_name:
        raise RemoteLeanError("remote deployment returned a different controller identity")
    marker = b'ELASTIC_MODULE = "lean_remote_elastic.py"'
    if content.count(marker) != 1:
        raise RemoteLeanError("worker controller binding changed; review immutable deployment")
    content = content.replace(marker, ('ELASTIC_MODULE = "' + controller_name + '"').encode())
    checksum = hashlib.sha256(content).hexdigest()
    result = ssh(config, ["python3", "-c", DEPLOY_WORKER, config["base"], checksum],
                 input=content, check=True, capture_output=True)
    target = config["base"] + "/bin/lean_remote_worker-" + checksum + ".py"
    if result.stdout.decode().strip() != target:
        raise RemoteLeanError("remote deployment returned a different worker identity")
    return target


def deploy_storage(config: dict) -> str:
    if "_storage_worker" in config:
        return config["_storage_worker"]
    content = Path(__file__).with_name("lean_remote_storage.py").read_bytes()
    checksum = hashlib.sha256(content).hexdigest()
    result = ssh(config, ["python3", "-c", DEPLOY_WORKER, config["base"], checksum, "lean_remote_storage"],
                 input=content, check=True, capture_output=True)
    target = config["base"] + "/bin/lean_remote_storage-" + checksum + ".py"
    if result.stdout.decode().strip() != target:
        raise RemoteLeanError("remote deployment returned a different storage identity")
    config["_storage_worker"] = target
    return target


def select_workspace(config: dict, workspace: str) -> None:
    if workspace == config["workspace"]:
        return
    selected = PurePosixPath(workspace)
    if selected.name != "lean" or selected.parent.parent != PurePosixPath(config["base"]) / "workspaces":
        raise RemoteLeanError("storage returned an invalid workspace")
    path = Path(config["_config_path"])
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != config["_config_sha256"]:
        raise RemoteLeanError("profile changed concurrently; preserve it and select the returned workspace explicitly")
    value = json.loads(raw)
    value["workspace"] = workspace
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")
        temporary = Path(stream.name)
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)
    config["_config_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
    config["workspace"] = workspace


def storage_command(config: dict, action: str, *, pins=None, seed=None, keep=False) -> dict:
    executable = deploy_storage(config)
    argv = ["python3", executable, "--base", config["base"], action,
            "--workspace", config["workspace"]]
    if seed:
        argv.extend(["--seed", seed])
    payload = {"owner": config.get("workspace_owner", config["source_root"]), "pins": pins, "keep": keep,
               "task_id": task_identity(config), "operation_id": config.get("_operation_id")}
    result = ssh(config, argv, input=json.dumps(payload), text=True, check=True, capture_output=True)
    observed = json.loads(result.stdout)
    if "workspace" in observed and action in {"prepare", "adopt", "use"}:
        select_workspace(config, observed["workspace"])
    return observed


def task_identity(config: dict) -> str | None:
    return config.get("task_id") or os.environ.get("R5_REMOTE_TASK_ID") or os.environ.get("CODEX_THREAD_ID")


def resource_options(config: dict, args: argparse.Namespace) -> dict:
    profiles = config.get("profiles", {})
    if not isinstance(profiles, dict) or any(name not in {"build", "lint", "cache", "plan", "phase"} for name in profiles):
        raise RemoteLeanError("profiles must map supported actions to resource settings")
    selected = profiles.get(args.remote_action, {})
    if not isinstance(selected, dict) or any(key not in RESOURCE_KEYS for key in selected):
        raise RemoteLeanError("action profile contains unsupported resource settings")
    # Compilation-capable phases use the same parallel budget as builds. Single
    # tools and compilation-forbidden phases retain their smaller envelopes.
    parallel = args.remote_action == "build" or (args.remote_action == "phase" and not args.forbid_compilation)
    values = {key: config[key] for key in RESOURCE_KEYS if key in config} if parallel else {}
    values.update(selected)
    values.update({key: getattr(args, key) for key in RESOURCE_KEYS if getattr(args, key) is not None})
    if any(type(value) is not int or value <= 0 for value in values.values()):
        raise RemoteLeanError("resource profile values must be positive integers")
    return values


def add_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--config", type=Path, required=True, help="local, untracked SSH/workspace configuration")
    actions = parser.add_subparsers(dest="remote_action", required=True)
    actions.add_parser("status", help="show server allocation and synchronized source identity")
    for action in ("prepare", "adopt", "release", "gc", "storage-status", "compact"):
        command = actions.add_parser(action, help="manage pooled workspaces and idle reclamation")
        if action in {"prepare", "compact"}:
            command.add_argument("--seed", help="existing idle remote package root used for incremental reuse")
        if action in {"prepare", "adopt"}:
            command.add_argument("--keep", action="store_true", help="retain this workspace across idle expiry")
    result = actions.add_parser("result", help="inspect or recover a known run without synchronization or compilation")
    result.add_argument("--wait", action="store_true", help="wait for a confirmed live worker to complete")
    result.add_argument("run_name", help="remote-UUID from the original build output")
    sync = actions.add_parser("sync", help="synchronize source inputs, preserving remote .lake caches")
    sync.add_argument("--include", action="append", default=[], help="additional in-package regular input file")
    sync.add_argument("--bootstrap", action="store_true", help="first cold basis only: transfer source before dependencies exist")
    for action in ("build", "lint", "cache", "plan", "phase"):
        command = actions.add_parser(action, help="run one scoped native Lake graph and retrieve its evidence")
        command.add_argument("--jobs", type=int, help="maximum simultaneous frontend processes")
        command.add_argument("--threads", type=int, help="native threads per frontend")
        command.add_argument("--lean-memory-mib", type=int)
        command.add_argument("--rss-limit-mib", type=int)
        command.add_argument("--allow-cpu-oversubscription", action="store_true",
                             help="explicit experiment: permit at most two single-thread frontends per effective CPU")
        if action == "build":
            command.add_argument("--allow-library-roots", action="store_true",
                                 help="explicitly requested whole-library build; permit named local root modules")
        if action == "phase":
            command.add_argument("--label", default="owned-phase")
            command.add_argument("--forbid-compilation", action="store_true")
            command.add_argument("--command", dest="phase_command", nargs=argparse.REMAINDER,
                                 help="owner-selected executable argv, after the module scope; no shell")
        command.add_argument("--include", action="append", default=[])
        command.add_argument("--release-workspace", action="store_true",
                             help="finish this task and release its workspace after confirmed process closure")
        command.add_argument("modules", nargs="+", help="qualified module targets; bare library roots are rejected")


def execute(args: argparse.Namespace) -> int:
    config = load_config(args.config, require_source_root=args.remote_action not in {
        "status", "result", "release", "gc", "storage-status", "compact"})
    if (args.remote_action == "release" or getattr(args, "release_workspace", False)) and not task_identity(config):
        raise RemoteLeanError("release requires a stable task_id, R5_REMOTE_TASK_ID, or CODEX_THREAD_ID")
    try:
        return execute_config(args, config)
    finally:
        if config.get("_operation_id") and not config.get("_operation_unconfirmed") and not config.get("_operation_closed"):
            try:
                storage_command(config, "finish-operation")
            except (OSError, ValueError, subprocess.SubprocessError) as exc:
                print("Invocation ownership retained: " + str(exc), file=os.sys.stderr)


def execute_config(args: argparse.Namespace, config: dict) -> int:
    if args.remote_action in {"prepare", "adopt", "release", "gc", "storage-status", "compact"}:
        from .lean_remote_storage import pin_data
        action = "status" if args.remote_action == "storage-status" else args.remote_action
        observed = storage_command(config, action,
                                   pins=pin_data(Path(config["source_root"])) if action in {"prepare", "adopt"} else None,
                                   seed=getattr(args, "seed", None), keep=getattr(args, "keep", False))
        print(json.dumps(observed, indent=2, sort_keys=True))
        return 0
    if args.remote_action == "result":
        from .lean_remote_result import recover_result
        return recover_result(config, args.run_name, wait=args.wait, ssh_runner=ssh)
    if args.remote_action == "status":
        result = ssh(config, ["python3", "-c", STATUS, config["base"], config["workspace"]],
                     check=True, capture_output=True, text=True)
        status = json.loads(result.stdout)
        # A source manifest is useful remotely; hundreds of hashes are not a status display.
        source = status.get("source")
        if isinstance(source, dict) and "files" in source:
            status["source"] = {key: value for key, value in source.items() if key != "files"}
            status["source"]["file_count"] = len(source["files"])
        print(json.dumps(status, indent=2, sort_keys=True))
        return 0
    if args.remote_action == "sync":
        sync_source(config, args.include, bootstrap=args.bootstrap)
        return 0
    allow_roots = getattr(args, "allow_library_roots", False)
    if any(MODULE.fullmatch(module) is None and not (allow_roots and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", module))
           for module in args.modules):
        raise RemoteLeanError("select explicit qualified module names, without options or whole-library roots")
    resources = resource_options(config, args)
    if args.remote_action != "build" and args.allow_cpu_oversubscription:
        raise RemoteLeanError("CPU oversubscription belongs only to build")
    if args.remote_action == "phase" and not args.phase_command:
        raise RemoteLeanError("phase requires --command followed by executable argv")
    source = sync_source(config, args.include)
    worker = deploy_worker(config)
    run_id = uuid.uuid4().hex
    run_dir = config["base"] + "/logs/remote-" + run_id
    command = ["python3", worker, "--base", config["base"], "--workspace", config["workspace"],
               "--run-dir", run_dir, "--expected-source", source]
    if task_identity(config):
        command.extend(["--task-id", task_identity(config)])
    if config.get("_operation_id"):
        command.extend(["--operation-id", config["_operation_id"]])
    for option, value in resources.items():
        command.extend(["--" + option.replace("_", "-"), str(value)])
    if args.allow_cpu_oversubscription:
        command.append("--allow-cpu-oversubscription")
    if allow_roots:
        command.append("--allow-library-roots")
    if args.remote_action == "phase":
        command.extend(["--label", args.label])
        if args.forbid_compilation:
            command.append("--forbid-compilation")
    command.extend([args.remote_action, *args.modules])
    if args.remote_action == "phase":
        command.extend(["--command", *args.phase_command])
    print("Remote evidence: " + run_dir, flush=True)
    config["_operation_unconfirmed"] = True
    result = ssh(config, command, capture_output=True, text=True)
    if result.stdout:
        # Worker stdout is a bounded completion summary; detailed Lake output is a file.
        print(result.stdout.strip(), flush=True)
    confirmed = False
    worker_code = result.returncode
    native_exit_code = None
    if result.stdout:
        try:
            summary = json.loads(result.stdout.strip().splitlines()[-1])
            confirmed = summary.get("run") == "remote-" + run_id and summary.get("group_closed") is True
            if confirmed and type(summary.get("exit_code")) is int and 0 <= summary["exit_code"] <= 255:
                worker_code = summary["exit_code"]
                native_exit_code = worker_code
        except (ValueError, TypeError):
            pass
    if result.returncode == 255 and not confirmed:
        print(json.dumps({"status": "transport_unconfirmed", "native_outcome": "unknown",
                          "run": "remote-" + run_id, "remote_evidence": run_dir,
                          "next_action": "result --wait " + "remote-" + run_id}), flush=True)
        return 255
    if confirmed:
        config["_operation_unconfirmed"] = False
    from .lean_remote_result import EVIDENCE, fetch_evidence
    delivery_code = fetch_evidence(config, Path(run_dir).name, EVIDENCE, native_exit_code=native_exit_code)
    if args.release_workspace and confirmed and not delivery_code:
        if config.get("_operation_id"):
            storage_command(config, "finish-operation")
            config["_operation_closed"] = True
        print(json.dumps({"workspace_release": storage_command(config, "release")}), flush=True)
    if result.stderr:
        print(result.stderr.strip().splitlines()[-1][:400], file=os.sys.stderr)
    return worker_code or delivery_code


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    add_arguments(parser)
    try:
        return execute(parser.parse_args(argv))
    except subprocess.CalledProcessError as error:
        from .lean_remote_result import _transport_error
        return _transport_error("Remote command transport/execution failed", error)
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print("remote_lean_error: " + str(error), file=os.sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
