# Native Lean artifact cache

Aglib, Quillen, Motivic and R5Lab enable Lean **4.34.1** Lake's native artifact cache with
`enableArtifactCache = true` and `restoreAllArtifacts = true` in their package
configuration. Lake shares immutable content-addressed artifacts and native
input-to-output mappings across checkouts and dependency positions. It restores
conventional `.lake/build` files needed by inventories and audits. Each checkout
still owns its project and dependency build directories; do not link writable
build trees between checkouts.

Mathlib retains its standard `lake exe cache get` interface and existing
resource-guard route. Native caching complements that service. Cache hits do not
establish current lint, axiom/control, inventory or replay
coverage. Use incremental builds and checks for actual gaps, retaining matching
evidence for unchanged closures; a historical receipt needs current-basis
validation before reuse.

## Local reuse

With the package's pinned elan toolchain, Lake normally selects its shared
toolchain cache automatically. `LAKE_CACHE_DIR=/absolute/path` selects an explicit
native cache for isolation or controlled reuse. Do not point it at another
checkout's `.lake/build`. Keep project/dependency build outputs private. Perform
the normal current-source build, using `--rehash` when importing cached outputs.
For a selected actual Aglib module, the guarded export route is:

```sh
lean-ci build --root . --rehash \
  --receipt-dir .lake/verification/my-leaf \
  --outputs /absolute/scratch/outputs.jsonl SELECTED_MODULE
lake cache stage /absolute/scratch/outputs.jsonl /absolute/scratch/staged
```

In another package containing Aglib as a dependency, import that native directory:

```sh
lake cache unstage /absolute/scratch/staged Aglib
```

Then run the consumer's normal guarded, rehashed build of its selected leaf.
`unstage` imports mappings under the named dependency's native scope. Lake's
current input traces, including source, imports, build options and compiler
identity, decide applicability. Different upstream pins can reuse unchanged
leaves while invalidating changed consumers. Lake owns all hashes and staging
files; the adapter does not implement a separate cache format.

## Upstream and toolchain updates

An upstream or compiler upgrade changes the required inputs; it does not itself
require local compilation. Keep compatible build trees and native cache entries,
obtain artifacts for the intended new inputs, then let the pinned Lake evaluate
the current graph with `--rehash`. A matching native cache can restore missing
ordinary outputs even under `--no-build`; that flag forbids the compilation
action, not matching artifact restoration.

Lake 4.34.1 traces the compiler Git identity and imported artifact hashes, along
with source, effective options, dependencies and platform inputs. It does not
identify a compiler merely by the `lean-toolchain` label, nor attest the bytes of
an arbitrary custom binary. A different compiler Git identity normally changes
required native keys. Matching artifacts produced for that new identity can
still avoid local builds. Successful loading of an old `.olean` is not an
independent cross-version compatibility guarantee: format/flags and compiler
build options affect the import checks. See the
[fixed native trace implementation](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Build/Module.lean#L580-L628)
and [fixed import reader](https://github.com/leanprover/lean4/blob/v4.34.1/src/library/module.cpp#L98-L136).

With Lean unchanged, a Mathlib change can preserve some downstream native import
hashes and change others. The actual compiled artifacts determine the result;
neither the upstream Git diff nor a description such as "private edit" proves a
particular reuse count. Mathlib's `lake exe cache get` uses a different source
hash system, including global root-configuration inputs. A global Mathlib cache
key change must not be confused with a proof that every downstream module needs
compilation. The [pinned Mathlib implementation](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Cache/Hashing.lean#L88-L149)
is the authority for its download keys.

Prepare the intended dependency revisions and matching toolchain before
validation. `lake update` and Mathlib's post-update cache hook are mutating
preparation operations; ordinary validation does not silently advance pins. If
the hook defers or is disabled, obtain matching cache with the intended toolchain
before the build. Downstream examples are explicit diagnostics with their own
package manifests; routine checks do not prepare or validate separate clients.

The [CI contract](CI.md) assigns complete current check scope for a dependency,
compiler or build-configuration transition. Compilation remains incremental and
cache-driven. Lint/axiom records have separate current-input keys; a build cache
hit is not their success evidence. Unknown unbounded checker-policy changes
require explicit current coverage or a validated migration.

Local compilation uses one native incremental Lake build. Successful lint,
entry, text and axiom results are retained by the [native local helper](../scripts/README.md)
against their actual command and inputs; unsupported or changed coverage is run
again. There is no separate local cache producer/consumer acceptance workflow.

## Shared CI protocol

Routine CI uses the [native reusable workflow](../.github/workflows/lean-ci.yml).
Build restores the current toolchain/manifest first, then the same toolchain
across manifest changes. Legacy exact-manifest and OS/architecture prefixes
also recover existing cache generations during the key-format migration.
Restored files are candidates: the ordinary `lake build --rehash` evaluates
current sources, imports, options and compiler identity before reusing outputs.
Each run still saves an immutable cache generation. Test restores this run's
Build outputs and retains its existing checks. If the optional Actions restore
misses or fails, Test restores Build's same-run native `artifacts/` and
`outputs/` snapshot, then obtains pinned Mathlib artifacts before overlaying the
mandatory current-run root archive. This includes unpublished dependency outputs
compiled by Build. The snapshot excludes package checkouts and working build
directories; streamed zstd compression avoids an uncompressed tar copy, and a
warm Test does not download it. Test keeps the same no-build production
verification. The Mathlib command is shared with Build through a YAML alias.
Quillen and Motivic pin this workflow independently of their mathematical
dependencies.

Before compilation, Build also imports published native caches for resolved
`kangxyz/*` Git dependencies, including inherited ones. It prefers exact producer
releases, then compatible recent seeds. Scoped assets carry producer identity
and compiler metadata, and mappings are registered under the dependency's own
Lake package name. Existing native release archives remain usable as legacy
seeds. Producer SHA and configured pin stay distinct. The
[workflow guide](../.github/LEAN_CI.md) owns the transport details. Partial progress
is saved through Actions caches; public releases still require successful Build
and Test. The cache transport adds no mathematical acceptance stage.

The [legacy composite action](../.github/actions/lake-cache/action.yml) and its
adjacent adapter below remain available for explicitly selected compatibility
operations; they are not used by routine CI.

Call the action with `mode: restore` after installing the pinned toolchain and
resolving the existing manifest, before the normal build. `root` selects a Lake
package in a larger repository. `repositories` is a whitespace-separated trusted
GitHub repository allowlist, for example `kangxyz/aglib kangxyz/quillen-k-theory`.
Only direct Git dependencies actually present in `lake-manifest.json` are
considered. Their names and exact resolved pins come from that manifest. No
application module names are encoded in common code.
The adapter separates a package's identity from its native manifest selector:
the single-component ASCII hyphenated spelling `«quillen-k-theory»` matches
TOML identity `quillen-k-theory`, while the original selector is passed to Lake.
Other Unicode, dotted and nested-quoted names are retained exactly.

Restoration first loads a runner-owned native Actions cache. Its fallback prefix
contains only OS, architecture and toolchain, independent of whole manifests and
package options. Every run/attempt saves a fresh immutable generation through
the caller's `always()` save step using the action's `cache-key` and `cache-path`
outputs. This preserves native mappings and partial progress across pin-only
changes. The existing checkout build-cache saves remain in place.

For each allowed upstream, the adapter first downloads a public asset from
`cache-<configured SHA>`. If unavailable or incompatible, it inspects at most 20
recent public releases and tries at most five matching cache prereleases as
seeds. A seed's cache tag and explicit release target identify its **actual
producer SHA**; draft, ordinary release, incompatible-platform and differently
targeted candidates are excluded. The asset's provenance must match the allowed
repository, package, actual producer revision, toolchain, full compiler version,
OS and architecture. Logs distinguish producer SHA from consumer pin. An
infrastructure-only upstream commit can therefore seed an older mathematical
pin without relabelling that producer's source identity. Native `unstage` and
the subsequent ordinary `--rehash` build decide which input mappings apply.
Unrelated artifacts remain available, while changed source/imports/options
invalidate their affected closure. A repository revision alone never authorizes
artifact reuse.

The default transport is public HTTPS and needs no cross-repository token.
Missing/expired assets, API limits, network failures or incompatible provenance
print an explicit cache miss and fall back to ordinary builds. Build and check
failures themselves remain failures. Trusted repositories and their publishers
are part of the artifact trust boundary; native cache import is not a fresh
kernel replay.

After guarded checks succeed, export root-package mappings with the same
`build_serial.py --rehash --outputs FILE TARGETS...` route. An up-to-date no-build
probe exports mappings without recompiling the library. On a main-branch push,
`mode: publish` runs native `lake cache stage`, adds honest source/compiler
provenance and uploads a pinned official Actions staging artifact with a unique
run/attempt name. The build job remains read-only to repository contents.

A separate `publish-cache` job depends on complete build-job success and alone
receives `contents: write` plus `actions: read`. It calls `mode: release` with
the build job's `artifact-name` output. The canonical helper downloads that
same-run staging artifact using `gh`, packs its unchanged flat files into a
standard `.tar.gz`, and publishes the platform/toolchain asset in a dedicated
`cache-<producer SHA>` prerelease. The tag targets that exact checked revision;
`--latest=false` preserves the project's ordinary release selection. Existing
assets are preserved without `--clobber`. Only normal producer `GITHUB_TOKEN`
permissions are needed; no new storage account, PAT or credential is required.
See GitHub's [release asset API](https://docs.github.com/en/rest/releases/assets#get-a-release-asset)
for public download access. The native Actions cache is still saved after
failed checks so partial progress can be resumed.

The workflows encode publication; configuring them does not prove that a remote
asset already exists or has been downloaded. Remote transport operation needs
evidence from successful producer and
downstream restore runs, such as the historical rollout recorded below.

The obsolete manual cache-client diagnostic has been retired. Its historical
results below retain their original producer and consumer basis; routine CI
now acquires native dependency caches through the shared workflow.

### Recorded initial rollout

Aglib infrastructure commit `b7713c414aacaad13d07b83d6bab1f0216191595`
passed [library and cache-publication CI](https://github.com/kangxyz/aglib/actions/runs/38772498398).
Its checks on that recorded source basis reused the existing compiled library,
and the native
cache release was published successfully.

The [real Quillen acceptance run](https://github.com/kangxyz/aglib/actions/runs/38775313932)
used Quillen `6fd36c20d05bc3dae38a474aae1eb93564614f35`, retaining its Aglib
pin `419bd685cee21ac408756fbfe99565be19d186fd`. Into an empty isolated native
cache, it anonymously imported the actual producer `b7713c4` and unpacked all
412 production Aglib modules under `--rehash --no-build`, with zero Aglib source
compilations. Tensor and Span import checks also passed. This records actual
cross-repository delivery and compatible reuse across an infrastructure-only
revision; complete Quillen verification belongs to its own library CI.

## R5Lab and future libraries

For a local R5Lab consumer, select a reviewed Aglib tooling checkout independently
of the mathematical dependency checkout. From R5Lab's `lean/` directory:

```sh
python3 "$AGLIB_CACHE_TOOLING/.github/actions/lake-cache/cache.py" --root . restore \
  --repositories kangxyz/aglib kangxyz/quillen-k-theory
```

This reads the existing manifest and does not update dependencies. Mathlib setup
and the selected leaf's normal checks still follow the consumer guide. R5Lab has
no producer workflow; this integration does not publish it.

A future TOML-configured library uses the same package options, reviewed pinned
tooling action, repository allowlist, ordinary guarded build with native `-o`
export, staging step, separate release job and native partial-progress save.
The pinned Lean 4.34.1 sources `Lake/CLI/Help.lean`, `Lake/CLI/Main.lean`,
`Lake/Config/PackageConfig.lean` and `Lake/Config/Env.lean` own native behavior.
In particular, `unstage` accepts an optional package argument even though its
brief help synopsis omits that argument.
