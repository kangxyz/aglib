# Evidence index

- Checkout: `/Users/kang/Documents/New project/tmp/work/jacobian/main-h1` at `58f0a8a22159d4bd7e9bdd03035494b394d95baf`.
- Files are byte-exact copies; Lean sources use `.lean.txt` names.
- Evidence is execution observation only; no mathematical acceptance is asserted.

## Source snapshots

- `sources/current/H1.lean.txt` — SHA-256 `c8eb3b35cf3e44b2320c94963377084d71c85e44c101aeca305256152fe7c6ef`; original `/Users/kang/Documents/New project/tmp/work/jacobian/main-h1/Aglib/AlgebraicGeometry/Cohomology/Group/H1.lean` (current protected H1 source).
- `sources/old-400k-wrapper/H1-bare-function-wrapper-proposed.lean.txt` — SHA-256 `036ab22b37ef44b790d3e17625fd45cf2b4d8bf1b54cf837bedd1de9a0086b04`; original `/private/tmp/r5-investigations/jacobian/canonical_source_rewrite/h1_adapter_applicability/H1-bare-function-wrapper-proposed.lean` (older proposed wrapper source).
- `sources/isolated-1m-diagnostic/H1.lean.txt` — SHA-256 `dfef97b7c92fb2414b7343af0e3ef0e1f288f1cd9604972e2200389fd70d63bf`; original `/private/tmp/r5-investigations/affine-kunneth/h1_sol_fallback/h1_mul_1m_probe/H1.lean` (isolated one-million diagnostic probe source).

## Runs

- `remote-ec77f579a84d435ba48c3f4ff0e170e7` — full400-failure; `source_content_sha256=25df09e545c752645ea8ab9b859a990f933db68bc8409f457cec024161c895d2`; H1 input `036ab22b37ef44b790d3e17625fd45cf2b4d8bf1b54cf837bedd1de9a0086b04`; receipt SHA `9b000962f868e7c80f24e16511a01af46392816014b91fd8d0dc33f6b8e1b36c`; status `failed`, exit `1`.
  - Started module `/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/Aglib/AlgebraicGeometry/Cohomology/Group/H1.lean` with native setup `/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/.lake/build/ir/Aglib/AlgebraicGeometry/Cohomology/Group/H1.setup.json` and argv `["/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/Aglib/AlgebraicGeometry/Cohomology/Group/H1.lean","-o","/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/.lake/build/lib/lean/Aglib/AlgebraicGeometry/Cohomology/Group/H1.olean","-i","/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/.lake/build/lib/lean/Aglib/AlgebraicGeometry/Cohomology/Group/H1.ilean","-c","/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/.lake/build/ir/Aglib/AlgebraicGeometry/Cohomology/Group/H1.c","--setup","/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/.lake/build/ir/Aglib/AlgebraicGeometry/Cohomology/Group/H1.setup.json","--json","-j4","-M49152"]`.
  - Finished with exit `1`.
- `remote-5b5fc8bb764f45edb0b9e05470e4b65e` — isolated1m-diagnostic-only-not-full-H1-pass; `source_content_sha256=25df09e545c752645ea8ab9b859a990f933db68bc8409f457cec024161c895d2`; H1 input `036ab22b37ef44b790d3e17625fd45cf2b4d8bf1b54cf837bedd1de9a0086b04`; receipt SHA `67f88ba20bf648f206e3f0de3ae8858d77d468cf340072d676fa003e6f7e4a53`; status `failed`, exit `1`.
  - Started module `/tmp/h1-final-phase-xhy6ulih/H1.lean` with native setup `/tmp/h1-final-phase-xhy6ulih/H1.setup.json` and argv `["/tmp/h1-final-phase-xhy6ulih/H1.lean","--setup","/tmp/h1-final-phase-xhy6ulih/H1.setup.json","--json","-DmaxErrors=1","-j4","-M49152"]`.
  - Finished with exit `1`.
  - Same source_content_sha256 as the 400k attempt; isolated diagnostic log records BEFORE_HMUL=945541 and AFTER=386241 (cost 559300), then logging-linter failure. This is not a full H1 pass.
- `remote-4d4518db3ddd4c598a14a4d01bba9e85` — full-current-native-pass; `source_content_sha256=9f50aee1d9e978fec856aa552bd8401f5946e8be1f01949e21f9677b6c85e33e`; H1 input `c8eb3b35cf3e44b2320c94963377084d71c85e44c101aeca305256152fe7c6ef`; receipt SHA `9efb2fd7bd3371989a6b6ba94e944b24e0ce7f622b1808cedfe4805d63d9a73d`; status `succeeded`, exit `0`.
  - Started module `/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/Aglib/AlgebraicGeometry/Cohomology/Group/H1.lean` with native setup `/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/.lake/build/ir/Aglib/AlgebraicGeometry/Cohomology/Group/H1.setup.json` and argv `["/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/Aglib/AlgebraicGeometry/Cohomology/Group/H1.lean","-o","/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/.lake/build/lib/lean/Aglib/AlgebraicGeometry/Cohomology/Group/H1.olean","-i","/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/.lake/build/lib/lean/Aglib/AlgebraicGeometry/Cohomology/Group/H1.ilean","-c","/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/.lake/build/ir/Aglib/AlgebraicGeometry/Cohomology/Group/H1.c","--setup","/root/autodl-tmp/lean-build/workspaces/managed-740a809c6061-315a5e4a9466/lean/.lake/build/ir/Aglib/AlgebraicGeometry/Cohomology/Group/H1.setup.json","--json","-j4","-M49152"]`.
  - Finished with exit `0`.
  - One fresh H1 frontend; event file retains started/finished records. Receipt records closed group, no input drift, and exit 0.

## Request and setup limits

Raw receipts preserve the recorded commands and input hashes. Compiler-event files preserve the actual native --setup paths and argv listed below. Separate setup JSON contents/hashes and separate request files were not present in these selected run directories; none are reconstructed.

Assignment identifies the current-vs-old H1 source change as the 400k-to-1m cap plus adjacent explanatory lines; both exact source snapshots are retained.
