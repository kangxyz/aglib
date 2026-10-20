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
