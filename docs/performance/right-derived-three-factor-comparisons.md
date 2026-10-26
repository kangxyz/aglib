# Right-derived three-factor comparisons across native branches

Date: 2026-10-26. This is the P0/P1 implementation pilot of the shared
sheaf/cohomology design. It applies the existing shared-constructor method and
records a reusable reconciliation of four native composition branches. The
measurements are actual in-package source compilations of two files, not
whole-library timings or measurements of an infinity-topos foundation.

## Original boundary and mathematical scope

The original etale scalar comparisons, Zariski projection formula and
closed-right-adjoint open locality each independently composed three factors:
the inverse source composition isomorphism, the derived ordinary isomorphism,
and the target composition isomorphism. Their concrete unit proofs repeated
cancellation and association after the module-sheaf categories were fixed.
The composition factors used different native constructors.

[Comparison/ThreeFactor](../../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/Comparison/ThreeFactor.lean)
now constructs that actual isomorphism over four variable categories. It proves
the whole original composite-unit equation before the component corollary.
The installed canonical composition comparison is identified, by its unit,
with the existing homology-preservation, injective-preservation, acyclic-image
and native `rightDerivedUnique` branches. The callers use the shared constructor
and retain named equalities with their original factors.

The etale client keeps arbitrary `Ring` coefficients, four independent
`HasDerivedCategory` records and genuine relative acyclicity of forgotten
module injectives. It does not assert that forgetting scalars preserves
injectives. The projection client retains finite locally free target
coefficients, arbitrary original D+ inputs, its existing local standard models,
and the proved `tensorPushforward_isRightDerived` condition. The locality client
retains its original open/closed pullback square and preservation branches.
The generic core installs no common derived model. No package budget,
dependency pin, linter suppression or mathematical hypothesis changed.

An actual mate consumer, `Exceptional/Derived/UnderlyingAdjunction`, previously
unfolded the old inverse-image comparison. Its single changed rewrite now uses
the proved `_eq_original` value law. This preserves the existing exact square
and original mate theorem rather than relying on the new constructor unfolding
to the old presentation. The other inspected production consumers use the
preserved public unit theorem or the unchanged isomorphism type.

## Matched source-compilation observations

Both runs used Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, baseline Aglib
`0ba24db0ca05a863d7d5630834316be36f03b7bf`, the same managed workspace and
jobs8/threads4 profile, compiler cap 12800 MiB and aggregate cap 110592 MiB.
The two actual files were compiled serially with prepared dependencies, using
the unchanged measurement driver
`22bd8c15a61718f7a7f465d6d2f712723dcfb89648200beb41e5259f95cb251e`.

For each actual in-package source, the native command was:

```sh
lake --no-build lean ACTUAL_SOURCE.lean -- -M12800 -j4 \
  -o FRESH_SCRATCH/caller.olean -i FRESH_SCRATCH/caller.ilean \
  -c FRESH_SCRATCH/caller.c
```

Pinned Lake resolves the real module/package and supplies its native
ModuleSetup, imported artifacts and library options. The dispatcher supplies
the unchanged package weak arguments explicitly. `lake lean` spawns the actual
source frontend even when its installed artifact exists. All outputs and
associated artifacts stay in fresh scratch directories; the installed caller
artifacts, dependency cache and traces were preserved. This is ordinary source
compilation, not kernel replay or a separate client check. The duration includes
Lake setup/import lookup and output generation, not just kernel CPU.

| Actual source | Before seconds | After seconds | Before peak RSS bytes | After peak RSS bytes |
| --- | ---: | ---: | ---: | ---: |
| `EtaleCohomology/Exceptional/Derived/Underlying.lean` | 118.369678 | 88.062638 | 5,192,253,440 | 4,277,923,840 |
| `Cohomology/ProjectionFormula/Basic.lean` | 13.439438 | 7.015110 | 2,897,518,592 | 2,615,500,800 |

The observed durations fell by 25.60% and 47.80%, respectively; peak RSS fell
by 17.61% and 9.73%. There is one successful observation per file per version.
The new generic producer separately compiled in 6.807 seconds. Its one-time
cost is not included in either caller's duration. The observations support
these actual consumers; they are not a repeated statistical experiment, a
whole-library saving, or evidence that every abstraction improves compilation.
No per-declaration profiler attribution was made.

## Exact source and execution evidence

Paths below the geometry directory are relative to
`Aglib/AlgebraicGeometry/`.

| Source | Before SHA-256 | After SHA-256 |
| --- | --- | --- |
| `EtaleCohomology/Exceptional/Derived/Underlying.lean` | `3e4547c3d4cd95cb313a6a292da249b382616215919aeaac9cf991e3d43ab4f3` | `9fb8e9008ea9cc367dad723066db017d5003a6ef93937ba5adf04378750f9e12` |
| `Cohomology/ProjectionFormula/Basic.lean` | `602a84b0d60983f2817b0122ad05da1fdad92008500d27f1d0cbd19f0fec64f7` | `ca858b2fa659fd66074e88ba1eec1b746ac065bcfd9c84b90fb911306b4905dc` |

The generic core SHA-256 is
`3897ad019c215da551867ba92fecea466fe07f39c3268d468600e926ab88abec`.
The additional locality source is
`a1a9fbf44424512e70687df76b6f53fe241eee547ad6a8e0038c36df16c339d6`;
it was compiled but no matched timing pair was requested for it. The mate
consumer repair is not part of either measured source or its import closure.

The local evidence owner is the research checkout's sibling
`pilot-p1/remote-runs/`; each named run contains its `receipt.json`, `build.log`
and `compiler-events.jsonl`. The corresponding remote logs remain under
`/root/autodl-tmp/lean-build/logs/`.
The complete per-command native results were also retrieved into the sibling
`pilot-p1/before-native-measurements.json` (SHA-256
`898056dcd5a2b2c0a69f0f6094e94c538f7557020fac911f5f2efbe0232f3e9d`)
and `after-native-measurements.json` (SHA-256
`4bdb19c5783cb9556dfaf12390843463ee87bb087c19a5c0e999c7a00542a93b`).

| Run | Actual scope and outcome |
| --- | --- |
| `remote-03cabb8310c24c7d857d23ad65f5dbac` | BEFORE: two successful serial source frontends; both original source hashes verified; source basis `2b617ed1a3a570f6fce500a343c9e00ff0b6d43404209a8960d3e14d3956f444` |
| `remote-1dcd24f4666649e68f1b7c010a57a295` | AFTER: two successful serial source frontends; source basis `341d603ad349e215647b4870183dfe368c1e086cc646b5499553686e0ccd9d83` |
| `remote-400ffebdb2034662a6e1fe1946aac736` | Generic producer compiled successfully at the stated hash |
| `remote-2140f7bea62b474fb80e098a576e3622` | Locality source compiled successfully; enclosing graph failed on the other two initial edits |
| `remote-e7b4d3cc4e2441328cddc10cfa34c518` | Current projection source compiled successfully; enclosing graph failed on the intermediate Underlying spelling |
| `remote-125e66a8c7b1450096fed260d1f113c3` | Current Underlying source compiled successfully, no diagnostics |
| `remote-cda012172fe04f12a5dc791369b89c58` | The one-line existing mate-consumer repair compiled successfully, no diagnostics; no matched timing claim |

The BEFORE and AFTER result files are under the actual managed workspace
`managed-d1ad007a676d-315a5e4a9466/lean/.lake/pilot-p1-measurements/`, in
`before-2562709291cc4f0fb09ac3950a5609ac/result.json` and
`after-489b946659544479a47b4b3b180e246f/result.json`. The initially cached
three-caller baseline `remote-89cbb1fc778542e1acb087cf3ab5db2b` had no newly
observed frontends and supplies no timing baseline.

## Failed edits and limits of the repair

The first projection integration bound the existing derivability proof at the
regular `derivedPushforwardPlus` alias. Typeclass search did not match the
literal native right-derived composite requested by the generic bridge. A
local instance explicitly typed at that same native functor expression fixes
the boundary. It adds no premise and changes no model. The initial Underlying
edit also failed a long-line check; a first wrap parsed a leading dot as a new
argument. Fully qualifying the same functor-isomorphism function fixes that
spelling. These were ordinary source/elaboration failures, not failed timing
observations or evidence of a new compiler-performance cause.

This pilot did not independently test an abstraction-only proof wrapper.
Earlier failed wrapper approaches and carrier diagnostics remain in the
[site-cohomology case](site-cohomology-share-the-comparison-definition-not-only-its-proof.md).
The present new ingredient is the common actual constructor with canonical
branch agreement and original-factor views. Its measurements do not establish
proper/smooth base change, descent, a complete six-operation system, or
downstream Motivic/Quillen compatibility. Those remain separately scoped work.
Independent mathematical review and final native checks retain their own
evidence; documenting this observation adds no replay or benchmark cycle.

## Final scoped validation

Native run `remote-8380c4565403488a8d48aadfb30571c5` completed successfully
on the five changed source origins and three actual terminal consumers. Text
style, native builtin commands, all 15 default declaration linters (46
declarations plus 30 generated declarations) and the pinned axiom audit
passed. The audit covered 5,462 production declarations in the actual closure
and used only `propext`, `Classical.choice`, and `Quot.sound`. Each native
builtin environment registry was empty, as its stdout states; the separate
declaration predicates were not empty or skipped. The local source-policy
check covered 7,201 Lean sources; the pinned generated-entry check passed.
The retained sibling `pilot-p1/final-native-result.json` has SHA-256
`79bdc747a4266e118f00670e6bc8b4bbd0309e0c9dbca98119ff6eb156811933`.
These are scoped acceptance results, not additional timing experiments.
