> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#affine-refinement-through-literal-mate-types) · [Context](original-context.md) · [Case index](README.md) · [Previous record](ambient-chart-pasting-and-affected-consumers.md) · [Next record](remote-resource-calibration-on-the-unchanged-library.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Affine refinement through literal mate types

The nonflat higher-image [affine refinement](../../Aglib/AlgebraicGeometry/Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineRefinement.lean)
originally completed its tactics but exceeded the kernel checking budget.
Its retained proof uses the original composite pullback/restriction adjunction
and global-section faithfulness on the original higher direct image.

Give the pointwise helper private qcqs instance parameters instead of four
proposition-valued lets inside its result. Fix the bundled ring and bare
higher-image indices of its evaluators and mates explicitly, including the
immediate section suppliers. The public theorem derives those instances from
its given open pullback squares.

A Type-valued datum constructor still exceeded its local 800,000-heartbeat
budget after those changes. Removing that datum and applying the generic
faithfulness and cancellation theorem directly to the literal native objects
and arrows passed: 53 seconds for the Lean leaf, 56.71 seconds for the guarded
build, and 3.07 GiB peak process-group RSS. The j1/M24576/RSS25600 profile and
finite local bounds were unchanged.

This establishes the combined interface and proof-encoding repair, without
isolating one kernel conversion or preprocessing operation as its cause.
The public proposition is byte-identical and adds no hypotheses or maps.

The downstream local-refinement paste also exhausted kernel and elaboration
budgets when local natural-isomorphism aliases were converted into component
arrows at the final paste. Its retained proof gives the original component
hom and inverse arrows explicit module-morphism types and proves the functor
and cancellation algebra abstractly. The concrete application then checks at
the standard 200,000-heartbeat budget. Keep the large functor-level types out
of the concrete local context when only their component arrows are needed.

The same typed-component and abstract-pasting approach checks the arbitrary-open
composition leaf in 27 seconds (31.01 seconds for the guarded build), with
3.43 GiB peak RSS. Its concrete private paste still exceeded 200,000 heartbeats
during elaboration after the ordinary type-boundary repairs; a documented
800,000 bound on that private declaration sufficed. Other declarations and the
process limits stayed unchanged. This is a bounded elaboration cost, distinct
from a failure of the kernel to accept a completed proof.

Fresh checks at the CI profile (`-j4`, native 12,800 MiB, group 13,824 MiB)
also passed. The flat affine comparison took 112.91 seconds at 7.92 GiB peak
RSS; affine refinement took 43.40 seconds at 3.05 GiB; the proper endpoint
module took 69.82 seconds at 3.94 GiB. A coherent 51-module check reused valid
outputs and actually rebuilt affine normalization, global flat agreement,
open composition, naturality and restriction in 136.35 seconds at 7.80 GiB.
Each accepted run exited zero with no guard failure and its owned group gone.
These are local CI-budget checks, separate from remote CI publication.

