# Schemes, module sheaves and cohomology

This family extends Mathlib's actual `AlgebraicGeometry.Scheme`, structural sheaves, over-categories and scheme morphisms. [SchemeOverField](SchemeOverField.lean), imported as `Aglib.AlgebraicGeometry.SchemeOverField`, defines `AlgebraicGeometry.Scheme.OverField.Base F := Spec F` and `FScheme F := Over (Base F)` for a field in universe `u`. A field scheme carries no implicit smooth, proper, integral or dimension-one hypothesis.

| Subject | Interfaces and principal results |
| --- | --- |
| [Modules](Modules/README.md) | Actual stalks/functors/base-change maps, quasicoherent affine comparison, finite presentations, exact vector bundles, coherent specialization, ordinary Picard tensor groups and differential maps |
| [Morphisms](Morphisms/README.md) | Etale stalk/neighborhood comparison, finite field-valued lift sets, finite-etale objects and base change, section rigidity, smooth regularity/dimension and proper graph modifications |
| [Properties](Properties/README.md) | Normal/domain stalks, component openness, connected integrality, qcqs affine induction and finite dense-affine covers |
| [Stalk](Stalk/README.md) | Actual stalk-map, flat-base-change, polynomial, generic-fibre and dimension comparisons |
| [Geometrically](Geometrically/README.md) | Geometric connectedness under field extension, algebraic-closure detection and proper geometrically integral constants |
| [Group](Group/README.md) | Actual group-object pullback, canonical identity/composition and multiplicative point-fibre comparison |
| [FunctionField](FunctionField/README.md) | Canonical generic inclusions, dominant field maps, generic-fibre isomorphisms and extension to targets integral over the base |
| [Generic finite-etale normalization](Normalization/GenericFiniteEtale/README.md) | Actual relative normalization and generic recovery, with separate normal/locally Noetherian finiteness and stalk conclusions |
| [BaseChange](BaseChange/README.md) | Scheme-valued coefficient pullbacks with original projections and naturality |
| [Spec](Spec/README.md) and [Products](Products/README.md) | Polynomial/Laurent spectra, coordinates and zero section, localization squares and integer-base product diagrams |
| [Limits](Limits/README.md) | Finite native over-products and arbitrary base-change comparisons |
| [IdealSheaf](IdealSheaf/README.md) | Actual kernel ideal modules, restrictions and canonical quotient-flat base-change maps |
| [EffectiveCartierDivisor](EffectiveCartierDivisor/README.md) | Finite presentation of invertible closed ideals and smooth relative-dimension-one Cartier criteria |
| [ProjectiveSpace](ProjectiveSpace/README.md) | Actual polynomial Proj, charts, twists, finite presentations, affine immersions, base change and chartwise Euler sequences |
| [Cohomology](Cohomology/README.md) | Actual Zariski `Sheaf.H`, structural scalars, Cech and derived comparisons, qcqs flat base change, proper coherent finiteness and projective duality |

Lower [commutative algebra](../RingTheory/README.md), [categorical structure](../CategoryTheory/README.md), [homology](../Algebra/Homology/README.md) and [topological sheaves](../Topology/Sheaves/README.md) supply the reusable prerequisites. [Root reading routes](../../doc/README.md) explain their interfaces. Curve/P1/genus/degree and K/G/Q/S applications remain external.

Godement and derived interfaces retain their bounds and original unit equations.
Proper coherent finiteness and smooth differential rank have proved suppliers;
the full arbitrary-base `LocalFreeCohomologyBaseChange` family remains an explicit
input, with the exact conditions recorded in [INTERFACES.md](../../doc/INTERFACES.md).
