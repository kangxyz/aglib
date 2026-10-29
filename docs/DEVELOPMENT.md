# Development and checks

Run from the package root with the committed `lean-toolchain`, `lakefile.toml`
and `lake-manifest.json`. Keep dependency upgrades explicit and separate from
ordinary proof work. Production imports use Mathlib and precise lower Aglib leaves.

## Mathematical trust

Claimed closed results require source correspondence, explicit hypotheses and
foundation inputs, no transitive `sorry`, and axiom dependencies limited to
`propext`, `Classical.choice`, and `Quot.sound`. Custom and native-computation
axioms cannot discharge a proof. Preserve production dependency boundaries and
identify source, pinned dependencies/toolchain and successful build coverage.
Independent mathematical review and writing acceptance retain their governing
requirements; conditional theorems retain their premises.

Native axiom auditing follows transitive dependencies from declarations defined
in production modules, including declarations in native mathematical namespaces.
It relies on successful compilation; it does not replay the kernel. Retired custom
auditor receipts additionally recorded checked-environment and inventory-control
predicates. They are not relabelled as executions of the upstream auditor.
Reuse actual compatible native build/check evidence and fill affected coverage.

## Normal task

In a prepared workspace, prove, compile the next coherent changed module and
repair from its diagnostics. For example:

```sh
lake build +Aglib.CategoryTheory.ExactCategory.Basic
```

Use an actual consumer when an interface question requires it. Keep compiler
checks enabled. Standalone final checks belong to final delivery; helper returns,
commits, merges and publication do not independently trigger another check cycle.
Keep matching caches and compatible successes. Missing artifacts or receipts do
not request whole-library rebuilding. Diagnose cache/source/pin mismatches before
building the genuinely required missing closure.

Keep stable constructors and independent expensive native proofs in separate
focused modules. Compile ready dependency branches concurrently and retain
matching producer artifacts when a consumer changes. When feedback on a slow
declaration is insufficient, isolate its statement formation, proof elaboration
and kernel checking using [targeted diagnosis](PERFORMANCE.md#diagnosis-and-evidence).
The next repair and compile should address that specific boundary while
preserving compatible successes and the original mathematical data.

## Local verification and CI

The local entry uses the same native mechanisms as the public workflow:

```sh
bash scripts/check.sh
bash scripts/check.sh --base ACCEPTED_COMMIT
bash scripts/check.sh --source-only
```

`--head`, `--full`, `--progress`, `--state` (or `--receipt-dir`), `--outputs` and
`--list` are native CLI options. A nonempty documentation-only change selects
source checks; clean/full native selection uses the package production roots.
`--list` describes commands without executing them. Keep progress/state outside
source deliverables. Compatible successful checks survive failures and resumed
work on unchanged inputs. The entry uses no GitHub accepted-baseline lookup,
recipe-hash admission, frozen request, replay or independent-client lifecycle.

The wrapper retains source layout/import/cycle, placeholder and source-option
checks. Native `mk_all` owns production entry generation and checking. The native
sequence builds production and package tests, checks generated entries and text
style, runs full-production builtin/declaration lint, and invokes the pinned
upstream production axiom auditor. Source guards do not replace transitive
axiom coverage. Test modules are discovered by Lake's in-package test glob; no
generated `AglibTest.lean` umbrella is required.

The ordinary direct commands are:

```sh
lake build Aglib
lake test
lake exe mathlib/mk_all --lib Aglib --check
lake --no-build exe mathlib/lint-style Aglib
lake --no-build lint Aglib -- --trace
```

Checker executables need prepared matching outputs. The native entry prepares
those tools and the upstream auditor under its guard; the exact pinned auditor
and public job boundaries are described in [native CI](../.github/LEAN_CI.md).
The configured package options and warnings remain unchanged. No duplicate
standalone test elaboration, custom origin-audit/control chain or downstream
preparation is appended to these commands.

## Setup and focused builds

Preserve the package pins and prepare only the dependencies/caches actually
needed by the selected imports. Mathlib retains `lake exe cache get` with explicit
module arguments when suitable. Use the [native cache protocol](CACHING.md) for
matching compilation artifacts. A cache hit is not mathematical acceptance.
Keep writable checkout/dependency outputs owned by their actual writer; do not
silently share mutable build directories across concurrent checkouts.

The installed `lean-tools build` command delegates one selected incremental module
graph to the shared package. For example:

```sh
lean-tools build --root . --state /absolute/fresh/build Aglib.Module.Name
lean-tools run --root . --receipt /absolute/command.json --capped-toolchain -- COMMAND
```

The package contains the source policies and library tools too; see
[the toolkit entry](../scripts/README.md). Managed remote execution preserves
its admitted `R5_LEAN_REMOTE_PROFILE`. Shared native artifact link metadata is
rechecked by content, so adding a hardlink in a peer workspace does not invalidate
a successful check. Real source/input changes still fail the relevant check.
The local native check set and independent axiom feedback follow CI; hosted job
transport and runner limits remain hosted concerns.

Mathlib's standard `maxHeartbeats` is 200000. Retained overrides must be positive,
finite and declaration-local, with an adjacent explanation. Do not use unlimited
`0`, global raises or new blanket allowances. Existing source guards retain the
option, import, naming and author-credit predicates.

## Incremental cache and publication

Keep native outputs and matching successful checks through repairs. Public CI
saves partial compilation independently of later checker outcomes; publication
consumes the successful run's staged mathematical compilation. Local checking
has no publication authority. A new checkout, commit or cache export does not
invalidate unchanged native evidence or assign mathematical acceptance.
The [public workflow guide](../.github/LEAN_CI.md) owns hosted job boundaries and
cache transport; [local tools](../scripts/README.md) owns retained script entries.

## Contribution conventions

Keep maintained text, identifiers, comments and documentation in English. Follow Mathlib source style and the [naming conventions](NAMING.md). Use the pinned Lean and Mathlib versions; dependency changes require their own coordinated update.

Current source author headers credit `kangxyz`. Credit actual contributors when they contribute; do not enforce a permanent single-author list or add blanket tool attribution. Preserve copyright and Apache 2.0 license notices. Keep historical source identities and correspondence in [REFERENCES.md](REFERENCES.md) and the existing migration records; current author credit does not erase provenance.

Update the owning family README when an object, namespace, hypothesis, result or canonical map changes. Keep cross-family architecture, development and provenance in `docs/`. New families need an admitted object or result and a current consumer, rather than empty scaffolding.

Preserve foreign changes and exact write ownership. Inspect `HEAD` and worktree status before writing and before staging or committing; coordinate overlapping edits and shared build outputs. Keep Git index and `HEAD` mutations serial. Do not push without an explicit current request.

Use incremental build, native/batch lint and relevant in-package tests during
development, integration and publication, preserving basic source correctness.
These execution checks do not discharge mathematical premises or independent
mathematical and writing review obligations.

## Downstream candidates for Aglib

During downstream development, place a new reusable general-theory implementation
that belongs in Aglib in the host library's `Aglib/` subtree:

| Source package | Source directory | Temporary module prefix |
| --- | --- | --- |
| R5Lab | `lean/R5Lab/Aglib/` | `R5Lab.Aglib` |
| Quillen | `Quillen/Aglib/` | `Quillen.Aglib` |

These are ordinary checked source modules with a prospective upstream owner.
Do not create a package-root `Aglib/` source tree in a downstream package: it
would compete with the actual dependency's `Aglib.*` module identities.

- Search Mathlib and the pinned Aglib API first. Reuse or extend their actual
  objects and maps. A candidate must state general algebraic geometry or related
  mathematical theory under its full hypotheses. Curve, projective-line,
  arithmetic and K-theory applications keep their downstream owners. General
  Milnor K-theory is an admitted algebraic family; its application comparisons
  remain downstream. Being
  useful in two applications alone does not select Aglib ownership.
- Mirror Aglib's mathematical hierarchy below the temporary prefix, following
  [architecture](ARCHITECTURE.md) and [naming](NAMING.md). Use native mathematical
  declaration namespaces from the start, such as `Algebra`, `CategoryTheory`,
  `CochainComplex` and `AlgebraicGeometry.Scheme`; the host prefix is a module
  location, not a declaration namespace. Do not add `R5Lab.Aglib`,
  `Quillen.Aglib` or `Aglib` wrappers around general declarations.
- Keep the candidate dependency closure general. Import focused Mathlib and
  Aglib leaves or explicitly designated candidate leaves, respecting the
  existing package dependency direction. Do not import ordinary host
  application modules. Isolate a required general prerequisite as a candidate
  first; keep application adapters outside the subtree. Coordinate one source
  owner when both downstream libraries need the same result.
- In each module docstring, name the intended `Aglib.*` module, describe the
  generality and actual hypotheses, and identify the current consumer. A
  family README records its interfaces and main mathematical results. A direct
  upstream contribution may skip the temporary location when it is already
  ready to integrate.
- Candidates use the host's normal source enrollment, Lean options, focused
  builds, lint and axiom policy. They are maintained proofs, not scratch or a
  place for placeholders. Put incomplete exploration outside production source.
  Add a focused client only for a meaningful uncovered interface condition.
- Move a ready, coherent candidate dependency group into Aglib, update its
  colocated guides and source provenance, obtain acceptance on the current
  identities, and then advance downstream pins. Retarget consumers to the
  upstream modules and remove the candidate implementation in the same
  downstream change. Preserve native declaration names when they still express
  the correct interface. Do not retain duplicate implementations or introduce
  a compatibility facade as the default migration route.

The two paths specify the candidate convention; create mathematical
subdirectories and source facades only when real candidate modules need them.
A temporary location does not itself assert upstream acceptance or a completed
migration.
