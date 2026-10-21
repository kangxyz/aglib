# Continuous Kummer classes

[Basic](Basic.lean) owns `GroupCohomology.Kummer`, the actual continuous
Kummer cocycle and class for a unit of an arbitrary field. The coefficient
is `Field.absoluteGaloisGroup.RootsOfUnity.Mu K n`, the additive form of the
actual roots in `AlgebraicClosure K`, with its discrete topology and continuous
absolute-Galois action. Cohomology is the existing
`GroupCohomology.ContinuousH1.H1` quotient.

For `0 < n`, a chosen nth root defines the cocycle `σ(a)/a`. Changing the
root changes the cocycle by an explicitly proved principal cocycle, so the
class is independent of the choice. Multiplication, inverses, vanishing on
nth powers, and the level-one case are proved on this same quotient. Neither
characteristic zero nor invertibility of `n` in the field is required here.

The current geometric consumer is the field Kummer comparison in
`AlgebraicGeometry/EtaleCohomology/Kummer`; its additional comparison hypotheses
remain with that owner. This group-cohomology construction does not assert
a Kummer isomorphism or an étale realization without those inputs.
