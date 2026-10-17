# Schemes, module sheaves and cohomology

This family extends Mathlib's actual `AlgebraicGeometry.Scheme`, structural sheaves, over-categories and scheme morphisms. [SchemeOverField](SchemeOverField.lean), imported as `Aglib.AlgebraicGeometry.SchemeOverField`, defines `AlgebraicGeometry.Scheme.OverField.Base F := Spec F` and `FScheme F := Over (Base F)` for a field in universe `u`. A field scheme carries no implicit smooth, proper, integral or dimension-one hypothesis.

| Subject | Interfaces and principal results |
| --- | --- |
| [Modules](Modules/README.md) | Actual stalks/functors/base-change maps, quasicoherent affine comparison, finite presentations, exact vector bundles, coherent specialization, ordinary Picard tensor groups and differential maps |
| [Descent](Descent/README.md) | Zariski stacks of module sheaves, quasi-coherent sheaves and line bundles; faithfully flat descent of closed subschemes |
| [Morphisms](Morphisms/README.md) | Etale stalk/neighborhood comparison, finite-surjective geometric-point lifting, closed-source Noetherianity and arbitrary-dimensional smooth regularity/normality/dimension |
| [Properties](Properties/README.md) | Normal stalks and locally Noetherian open-component/integrality results |
| [Stalk](Stalk/README.md) | Actual polynomial and generic-fibre local-ring comparisons |
| [Geometrically](Geometrically/README.md) | Geometric connectedness under arbitrary field extension and algebraic-closure detection |
| [Group](Group/README.md) | Actual group-object pullback, canonical identity/composition and multiplicative point-fibre comparison |
| [Cohomology](Cohomology/README.md) | Actual Zariski `Sheaf.H`, structural scalars, affine/finite-support/Noetherian vanishing, Cech comparison, canonical field base change and explicit finiteness/relative inputs |

Lower [commutative algebra](../RingTheory/README.md), [categorical structure](../CategoryTheory/README.md), [homology](../Algebra/Homology/README.md) and [topological sheaves](../Topology/Sheaves/README.md) supply the reusable prerequisites. [Root reading routes](../../doc/README.md) explain their interfaces. Curve/P1/genus/degree and K/G/Q/S applications remain external.

[Spec](Spec/README.md) and [Products](Products/README.md) add actual polynomial/Laurent and integer-base product diagrams. Scheme properties include the actual quasi-compact category and the affine-induction principle with explicit overlap/union premises. Latest Godement and derived interfaces retain their bounds and unit equations and do not discharge the older explicit rank/finiteness input families.
