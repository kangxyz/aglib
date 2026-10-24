# Lean development toolkit

All shared implementations and library-specific tools live in one installable
`lean_tools` package. Install it once from the selected Aglib checkout:

```sh
python3 -m pip install /absolute/path/to/aglib/scripts
lean-tools check --root /absolute/package
lean-tools build --root /absolute/package --state /absolute/fresh/build Module.Name
lean-tools run --root /absolute/package --receipt /absolute/command.json -- COMMAND
```

Python 3.11 or newer is required; the toolkit uses the standard library. An
explicit source checkout also works with `PYTHONPATH=/absolute/aglib/scripts
python3 -m lean_tools ...`. Existing `scripts/check.sh` and the downstream libraries'
thin launchers select this same package. Explicit `LEAN_CI_TOOLING_ROOT` and
`MOTIVIC_TOOLING_ROOT` selection remains supported. Migrated launchers require
toolkit 0.3.1 or newer, so an older installation cannot silently omit library
source policies. No second executor, cache
scheduler, frozen request or script-hash approval protocol is retained.

The console command is `lean-tools`; the existing `lean-ci` command is an alias
to the same function. The distribution keeps the installation name
`lean-incremental-ci` so existing installations can be upgraded in place.

`check` selects Aglib, Quillen or Motivic policy from the package's Lake name;
its explicit Python API still supports R5Lab and other callers. It uses the
same production build, checker preparation, generated-entry, text-style,
in-package Test, declaration lint and pinned production axiom audit as CI.
Ordinary check failures retain compatible successes and collect independent
axiom feedback. Failed Build or a real source/input change cannot produce a
successful final result. `--list` prints the commands, `--source-only` limits the
request to existing source guards, and `--base`/`--head`, `--progress`, `--state`
and `--outputs` retain their existing meanings. `--full` does not force rebuilding.
Hosted cache transport and runner/job limits remain in the public workflow.
Library selection and resource-variable aliases are data in `library.py`; all
libraries share one check/build/run/cache implementation. The named subpackages
contain their differing source-boundary rules and topic generators.

`build` delegates one incremental graph to Lake, preserving matching compiled
artifacts. `--no-build --outputs PATH` exports already available native mappings.
`run --capped-toolchain` uses the same resource implementation; `run
--bootstrap-cache -- lake exe cache get [MODULE...]` acquires Mathlib/Batteries
cache roots without a library-specific compiler wrapper. Managed remote resource
profiles retain the parent's admitted compiler and concurrency limits.

## Library tools

| Command | Existing operation |
| --- | --- |
| `lean-tools aglib layout` | Aglib source graph, exports, import boundaries and cycles |
| `lean-tools aglib layout --generate Aglib.Topic` | Generate one occupied topic; native `mathlib/mk_all` owns production roots |
| `lean-tools aglib placeholders` / `policy` | Existing placeholder, source-safety, author and finite-heartbeat predicates |
| `lean-tools quillen layout` / `placeholders` / `imports` | Quillen policy and unchanged topic generation |
| `lean-tools cache --root PACKAGE [MODULE...]` | One scoped Mathlib cache implementation for every library |
| `lean-tools motivic repository` / `imports` | Motivic policy and topic generation |
| `lean-tools motivic build` / `client` | Explicit existing module/export and client helper requests |

The existing `quillen cache`, `quillen cache-sources`, `motivic cache` and
`motivic cache-bootstrap` command forms dispatch to the shared cache module.
Dependency resolution runs only with `--resolve-deps`; prepared workspaces do
not repeat it for every cache request. `--list` is read-only, `--guarded` uses
the shared resource implementation, and empty scopes never request all Mathlib.

Historical extraction inspection is the Python API
`lean_tools.aglib.migration.read_source`; it still requires original source revision
and content hash. Retired extraction writers remain disabled. Historical
performance records retain their original command names; current invocations
are documented here.

## Input identity and reusable results

Successful checks retain their actual command, checker, source, environment and
native-content bindings. Shared `.olean`/`.ilean` hardlinks can change ctime
without changing bytes: this invalidates the cached content hash, then identical
content and lookup identity preserve the check result. Inode, mtime, mode,
content, symlink, disappearance and import-shadowing changes remain guarded.
Source/configuration observations retain strict temporal guards. Native evidence
has CI's trusted-producer content-correspondence contract at observation
boundaries; it does not certify uninterrupted absence of transient native writes.
Moving these Python tools does not by itself invalidate compatible native checks.
No kernel replay, separate client validation or new acceptance chain is added;
independent mathematical review and writing acceptance retain their requirements.

All Python tests, including the three libraries' migrated policy/tool tests,
live under `scripts/tests/`:

```sh
PYTHONPATH=scripts python3 -m unittest discover -s scripts/tests
```

The hosted-workflow tests additionally use PyYAML, tar and zstd. These bounded
tests exercise orchestration and content/reuse behavior; they are not a complete
Lean library build or mathematical acceptance evidence.
