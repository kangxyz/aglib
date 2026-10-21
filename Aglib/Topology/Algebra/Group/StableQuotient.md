# Continuous actions on stable additive subgroup quotients

`StableQuotient.lean` exposes `AddSubgroup.StableQuotient`.

For an arbitrary group G acting additively on M and an actual additive subgroup R, the supplied
condition that every g maps R into R constructs the quotient action. The quotient has the usual
topology. Joint continuity descends along its open quotient projection, and that same
projection is a continuous equivariant coefficient map. No closedness, Hausdorffness, or
automatic stability statement is assumed.

The carrier is the actual additive subgroup quotient `M ⧸ R`; the coefficient map
is its canonical continuous projection in `GroupCohomology.ContinuousH1.CoefficientMap`.
The source-private additive maps are local terms in the exposed quotient action.

Source: `R5Lab.Aglib.TopologicalGroup.StableQuotient`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`82647b23bac6372af9ada37107ddbd65bd4833d5d14b290b3e030677686f3e1f`.

Source correspondence and compilation coverage have separate records in the assigned
scratch handoff; this document does not assign mathematical closure status.
