# Torsion levels and compatible towers

`Levels` uses Mathlib's `AddSubgroup.torsionBy` and proves its equality with the
literal natural multiplication kernel. `Equivalence` restricts an actual additive
equivalence without changing its underlying element. `Finite` deduces finiteness
at positive levels from the prime levels dividing them, and preserves the full
group at level zero. `FiniteCharacters` requires an explicit injective detector.

`Detectors` constructs coprime coefficient detectors with the actual CRT map and
assembles prime-power detectors into all positive levels. The prime-power
injectivity assumptions remain inputs. `BoundedTower` proves vanishing from a
uniform exponent and compatible transitions; `FiniteKernel` constructs that
bound inside a finite kernel and proves equality of compatible torsion towers.
No arithmetic or geometric realization is supplied.

The split additive quotient consumer is
`Aglib.Algebra.Group.NormalizedQuotient`; character consumers use the original
finite coefficient groups rather than replacement torsion carriers.

`AddSubgroup.TorsionBy.InjectiveLevelDetector` records the constructed map and
its injectivity proof. The public construction data are shared by the exposed
assembled map and its injectivity theorem; prime-power realization and
injectivity still have to be supplied.

[RankTwo](RankTwo.md) constructs coordinates from the cardinalities at every
positive divisor level, using the literal torsion subgroups and canonical
coprime maps. Cardinality at the top level alone is not its hypothesis.
Its `basisOfEquiv` retains an existing `ZMod n` scalar action.

The geometric consumer [MultiplicationTorsion](../../AlgebraicGeometry/Group/MultiplicationTorsion.md)
constructs a `Module.Basis (Fin 2) (ZMod n)` on the literal
`MultiplicationKernel.finiteTorsionPoints E n`, under `hE : Curve.Properties E.X`,
the native `coherentGenus F E.X = 1`, `0 < n` and `IsUnit (n : F)` hypotheses.
The scalar action is canonical; the existing Galois action is linear and the
actual level maps have their canonical semilinearity. Level one is included.
No Galois equivariance of the selected basis or perfect pairing is asserted.

[Rank](Rank.lean) gives native coordinates for positive `n` when every divisor
`d` of `n` has `#T[d] = d^r`, including rank zero and `n = 1`; no canonical
basis is asserted. [RankTwo](RankTwo.lean) specializes the same construction.
