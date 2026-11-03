# Coarse source-preserving validation under a mapping limit

**Validated on 2026-11-03.** All seven producer batches have successful lint
and approved-axiom coverage, retaining six unchanged import closures. Neither
original single whole-root command passed.

## Failure and retained environment

On the original Linux host, `vm.max_map_count` was 65530. Whole-root native lint
and the pinned axiom audit failed during import loading, although the artifacts
were present and readable. A sampled audit reached 65532 mappings, with no
observed OOM. The host denied the sysctl change. This identifies an observed
execution boundary, not a unique explanation for every native loader read error.
The earlier [loader diagnosis](../../loader-fallback-read-diagnosis.md) retains
the failing branch and observations. A separate upstream toolchain-build attempt
was stopped and its output was not adopted.

The working method retains Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Batteries
`f2effa3d803fda822b1f97b806c47cf2adfbcbc2`, original package options, existing
suppressions and the pinned auditor. The workaround changes no mathematical
proof, dependency pin or CI workflow.

## Coarse batching

The [plan](evidence/plan.json) assigns 9357 implementation modules disjointly to
seven batches. Their union covers the production implementations; 15 generated
import-only entries contain no declaration commands and retain native source,
entry-generation and style coverage. Batch assignments contain 2396, 1088, 236,
589, 1414, 3471 and 163 modules. The first six import closures each contain 4500
Aglib modules; the seventh contains 163. Import dependencies may overlap.

Each process imports one private-level environment for its entire batch. The
lint frontend selects declarations by their actual `const2ModIdx` origin,
including private, auxiliary and automatically generated declarations. Its two
dedicated workers use chunks of 64 with the pinned 15 normal and slow
Batteries/Mathlib rules and their original predicates. The rule set is asserted;
an unexpected registration fails. Existing `nolint` and `scripts/nolints.json`
semantics are retained.

Native environment linters retain captured source options. The pinned registry
was empty, and an unexpected registration fails. Native persisted text logs are
collected for assigned modules without overriding source options. Native deferred
checks preserve captured options and mark nonassigned imported modules checked.
The legacy launcher initializes runtime and meta dependencies. Up to three batch
processes ran concurrently; this is separate from the two workers inside each.

The unchanged auditor checks full private environments of the actual batch
imports using its original approved-axiom predicate. Dependencies overlap across
audit batches. Its revision is `46024e005996495c65ef609368e11ab39c4222e3` and
binary SHA-256 is
`03ce70017a1ee8848c74541b00b29b40e471527ff7484e389b3623850dd08743`.
The lint frontend binary SHA-256 is
`5780ba3ac09621d48b0717eef95fe2324091e19463307e53dd22082c8a7a5d61`.

## Source identities and repairs

The original plan SHA-256 was
`1506063b568e40f7e3cf4dc29aec29b8d8339d20adf0aa84a1691d8b85d6632f`,
with native source digest
`b4c9712b2f89b5cd52590dee356d8e2af5e649336e5f9db6f717d3666d9496d5`.
Original audit `remote-c9d549ca12d34816bd8a601f196fe960` passed seven batches.
Initial lint runs `remote-cd5260b5159144f78c3f49173f6c6935` and
`remote-be6d09935dc2447291869c28645f6634` checked 130278 declarations and found
104 issues: 41 definition names, 52 missing docstrings and 11 declarations with
unused arguments. Repairs stay within the migration and preserve proof constructions,
actual maps and required hypotheses; direct consumers are updated with them.

On native source
`176410f68cfa3594d81434b1e85921d98ee5ed53b65bc8a9fbeaa1f055f85a5d`,
`remote-1bdbf01bf1dc4331b4a2858cc6f75bb0` passed six lint batches and all
seven audit batches. Batch 05 found one further unused `Nonempty U` premise in
normalization-chart localization. The premise and its now-redundant direct
consumer premise were removed together; both original proof bodies remain.

The final native source digest is
`f83e4561558ff9a7aa384c05978446c03bee6655e816001ad1e0718b2548fdba`.
Its full assignment plan SHA-256 is
`6f850f21fd7180a7ece28fc5d1e2651606f76cabfb573e2fbbef87e0af00f66a`.
The [input delta and dependency impact](evidence/input-delta.json) record exactly
two changed native inputs among 10487, both in batch 05's import closure and
outside the other six. Their matching successful lint and audit results are
retained. `remote-6946cf49733c4e27ab68ce7be33b7e91` passed the recheck of batch 05
on the final source. This reuse is based on unchanged actual inputs, not a commit or
phase boundary.

## Validation results

All seven lint batches have zero declaration, environment, text or deferred
findings. All seven audit batches use only the three approved foundations, with
no violations. The [result summary](evidence/validation-results.json) records
130278 declarations, exact run/source identities and retained closure coverage.
The complete production build, native style and in-package tests passed in
`remote-f3f83ac4dcd84c599bffd2647fb5e434`.
The incremental production build used six frontends, all successful; native
style took 8.71 s and cached in-package tests took 5.99 s. Earlier successful
source-policy and generated-entry coverage is retained; the final repair changes
no imports, module enrollment, source options or proof bodies.

Exact checker/config snapshots and launch scripts are retained under
`evidence/`. Archived Lean sources use `.lean.txt` and are not enrolled as
production Lean modules. The configuration's absolute Mathlib path records the
original prepared workspace. Complete remote logs and receipts remain under
`/root/autodl-tmp/lean-build/logs/<run>/`, and retrieved copies are owned by this
integration's local output directory.

The resulting coverage is producer-module coverage across batch environments.
It is not execution of the old single whole-root environment, a proof of
identical global environment-sensitive behavior, or a controlled speedup claim.
No kernel replay, separate mathematical client or replacement toolchain was used.
