> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#ci-cache-reuse-across-dependency-updates) · [Context](original-context.md) · [Case index](README.md) · [Previous record](repair-workflow.md) · [Next record](local-validation-and-shared-artifact-link-metadata.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## CI cache reuse across dependency updates

[Quillen run 39969720587](https://github.com/kangxyz/quillen-k-theory/actions/runs/39969720587)
missed the whole-manifest Actions cache after upgrading Aglib and logged 3424
successful builds before its runner shut down. No Lean compilation error was
reported; cache saving was skipped after the shutdown. The shutdown cause is
unknown. Commit `5489643` had removed the separate toolchain-scoped restore,
leaving only exact toolchain/manifest recovery.

The existing restore now prefers matching pins, then the same Lean toolchain,
with legacy-key fallbacks so adoption can recover already saved generations.
The ordinary build uses `--rehash`; Lake decides applicability from current
inputs, rather than a GitHub cache hit establishing validity. Workflow fixtures
cover changed pins, legacy keys, preference order and platform separation.
This repairs cache selection, not runner shutdown or proof elaboration costs.

The first repair covered only same-repository Actions restoration. The native
migration had also removed Quillen's upstream-release import in `95270559`,
while the shared publisher retained a different `lean-native-*` format. Restoring
Quillen's older cache therefore did not acquire newly available Aglib outputs.
The shared native workflow now connects that publisher to manifest-discovered
upstream downloads, exact-pin/recent seeds and dependency-scoped `unstage`.
The native `-o` exporter records root-package outputs only, so inherited upstream
packages must be fetched separately too.

A bounded Lean 4.34.1 fixture exercised the actual workflow's stage, publication,
download and import commands for all three package scopes, with GitHub storage
replaced by a local transport fixture. A fresh consumer reused all three core
modules with `--no-build --rehash`, including an older Aglib producer at a newer
consumer pin. Its changed Aglib leaf correctly failed the no-build request and
compiled only that leaf. Forty workflow tests cover transport fallbacks and
identity, archive handling, immutable publication and existing check boundaries.
These are scoped transport/reuse results, not a whole-library CI pass or a timing
claim. The fix does not identify or prevent the earlier runner shutdown.

