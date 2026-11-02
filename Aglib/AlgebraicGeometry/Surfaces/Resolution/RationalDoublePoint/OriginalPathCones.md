# Geometry and full cones on the original path

API: [original_path_geometry_and_cones](OriginalPathCones.lean#L81).

## Interface

`original_path_geometry_and_cones` works on the existing
`Arc.ClosedPointBlowupPath`. It assumes the initial stalk is normal, Nagata,
two-dimensional and universally rational. It takes as input a generating
triple and a supplied nonzero homogeneous quadratic generating the
**entire** original canonical cone-map kernel, over the original residue field. In the contradiction branch, every selected original
stalk is nonregular.

For every original stage it derives normality, Nagata, dimension two,
universal rationality, cotangent rank three and an actual full quadratic
cone on a genuinely generating triple. No later Hilbert function, canonical
frame, Gorenstein structure, kernel, marking, arc or termination is an input.

## Construction and original maps

The private geometric induction uses `PointLocalization` on each literal
`P.datum n`, then the actual ordinary normal/rational blowup and original
singular-stalk propagation. The resulting native stalk equivalence transports
normality, dimension and rationality to `P.localRing (n+1)`. Nagata transport
uses the existing finite-algebra theorem for that actual equivalence.

The cone induction uses the single weakest full-kernel classifier. A Case-I
parent and the actual next singular child give a good parameter and then a
true original fixed-parameter successor. A Case-II parent gives actual child
three-generation and cotangent rank three **before** Hilbert numerics. The
existing first-power exceptional theorem gives the full Hilbert function on
that literal child ring, and the unique native full-kernel producer supplies
its quadratic. No associated-graded ring is silently replaced during this
argument.

## Boundaries

The initial full cone remains supplied data. `OriginalMixedPath` uses the
derived cones on the same original path to construct a marked tail.
`FiniteHeight` and the finite-resolution endpoints retain their explicit
initial-cone and earlier-complete-base hypotheses.

Present consumers: [OriginalMixedPath](OriginalMixedPath.md).
