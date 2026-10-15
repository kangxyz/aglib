# Native Lean artifact cache

Aglib, Quillen and R5Lab enable Lean **4.34.1** Lake's native artifact cache with
`enableArtifactCache = true` and `restoreAllArtifacts = true` in their package
configuration. Lake shares immutable content-addressed artifacts and native
input-to-output mappings across checkouts and dependency positions. It restores
conventional `.lake/build` files needed by inventories and audits. Each checkout
still owns its project and dependency build directories; do not link writable
build trees between checkouts.

Mathlib retains its standard `lake exe cache get` interface and existing
resource-guard route. Native caching complements that service. Cache hits do not
replace current builds, linters, axiom controls, inventories or kernel replay,
and historical verification receipts do not become current evidence.

## Local reuse

With the package's pinned elan toolchain, Lake normally selects its shared
toolchain cache automatically. `LAKE_CACHE_DIR=/absolute/path` selects an explicit
native cache for isolation or controlled reuse. Do not point it at another
checkout's `.lake/build`. Keep project/dependency build outputs private. Perform
the normal current-source build, using `--rehash` when importing cached outputs.
For a selected actual Aglib module, the guarded export route is:

```sh
python3 scripts/build_serial.py --rehash \
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

## Shared CI protocol

[The composite action](../.github/actions/lake-cache/action.yml) and its adjacent
Python adapter are the single implementation. Tooling revisions are pinned
independently of mathematical dependency revisions. Quillen checks out the
tooling separately; enabling the protocol does not upgrade accepted mathematics.

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
asset already exists or has been downloaded. The first successful producer run
and downstream restore must establish remote transport operation.

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
