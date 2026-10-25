> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#cohomology-cone-legs-specify-the-actual-scheme-endpoints) · [Context](original-context.md) · [Case index](README.md) · [Previous record](relative-section-scalars-name-the-actual-transport-before-evaluating.md) · [Next record](original-tuple-cochains-normalize-typed-carriers-before-transport.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Cohomology cone legs: specify the actual scheme endpoints

In graph139, `DiagramCohomologyCocone` inferred the target scheme of a cone
projection as `((Functor.const I).obj c.pt).obj i`. Searching for `HasExt`
on that expression expanded to localized-Hom instances and exhausted the
20,000 typeclass synthesis heartbeat limit. A later equality also reached
the separate 200,000 elaboration heartbeat limit; subsequent cocone errors
were cascading and were not evidence of a mathematical obstruction.

Specify the source stage scheme and the actual target `c.pt.unop` explicitly
in `cohomologyTransfer` and `cohomologyTransfer_triangle` applications. This
selects the existing `HasExt` instances without unfolding the constant diagram.
Keep the Ext universe independent of the scheme and coefficient universes.
For cocone naturality, compose the typed equation with `Category.comp_id`
rather than asking simplification to identify opaque cohomology objects.
Graph141 accepted the complete cocone leaf in 43 seconds on 37cce7b after
these changes and an ordinary `colimit.ι_desc` argument correction. No budget
or transparency option was changed; no extra benchmark, test, audit or kernel
replay was run. This records a validated repair, not a comparative speedup.

### Fixed pullback systems: compose transformations before evaluating coefficients

The fixed-coefficient inverse scheme system encountered kernel excessive-memory
failures in its native transition composition proof (compiler graphs 141 and
142). A separate concrete `congrArg` transporting the adjunction composition
comparison also reached the unchanged `whnf` limit. The generic mate constructor
and abstract scheme-triangle laws themselves were already accepted; the expensive
boundary was their simultaneous specialization to indexed scheme maps and an
actual sheaf coefficient.

In `EtaleCohomology/Stalk/PullbackCoefficientSystem.lean`, the successful repair
first proves the triangle composition as an equality of whole natural
transformations, specializes that equality to the diagram, and evaluates it at
the coefficient only once. `System.ofLeftMapsWithComparisons` transports the
specified identity and composition isomorphisms at the abstract adjunction
boundary, rather than constructing a large concrete component-level `congrArg`
inside the native system definition. The original inverse-image triangles and
adjunction comparisons are unchanged.

The exact repaired leaf passed the normal production build in graph 144 (97 s).
This is evidence of acceptance after the diagnosed failures, not a benchmark or
a claim that compilation is optimized. No limits, elaborator options, kernel
replay, or additional validation runs were introduced for this repair.

