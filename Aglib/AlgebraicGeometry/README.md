# Schemes, module sheaves and cohomology

This family extends Mathlib's actual `AlgebraicGeometry.Scheme`, structural sheaves, over-categories and scheme morphisms. [SchemeOverField](SchemeOverField.lean), imported as `Aglib.AlgebraicGeometry.SchemeOverField`, defines `AlgebraicGeometry.Scheme.OverField.Base F := Spec F` and `FScheme F := Over (Base F)` for a field in universe `u`. A field scheme carries no implicit smooth, proper, integral or dimension-one hypothesis.

| Subject | Interfaces and principal results |
| --- | --- |
| [Modules](Modules/README.md) | Actual stalks/functors/base-change maps, quasicoherent affine comparison, finite presentations, exact vector bundles, coherent specialization, ordinary Picard tensor groups and differential maps |
| [Compactification](Compactification/README.md) | Schematically dense compactification of separated finite-type morphisms over qcqs bases, with the original open immersion and proper factorization. |
| [Approximation](Approximation/README.md) | Actual arithmetic systems for qcqs schemes, closed finite-presentation hulls, and proper fixed-base approximation over arbitrary affine schemes. |
| [Descent](Descent/README.md) | Zariski module stacks, fpqc quasicoherent and fppf line-bundle stacks, and closed-subscheme descent along flat surjective quasi-compact maps |
| [Over S representability](Sites/OverRepresentability.lean) | Zariski-local representability on `Over S` for presheaves in any universe (`OverSubfunctorCover.representableByGlued`; Stacks 01JJ relative to `S`), on full subcategories of a property that passes to open immersions and is local for open covers (`IsOpenLocal`), such as locally Noetherian test schemes (`SubfunctorCover`, `isRepresentable_of_isLocallyNoetherian`), representability of an open subfunctor of a representable functor by the open subscheme of the representing object attached to the universal element (`representableByRestrictOpens`, `IsOpenSubfunctor.representableBy`; Stacks 01JI, property (*)), and locality on the base (`overZariskiLocalRepresentability`) [Fppf](Sites/OverRepresentability/Fppf.lean): the Zariski topology is coarser than the fppf topology on schemes and on `Over S` (`Scheme.zariskiTopology_le_fppfTopology`, `Scheme.zariskiTopology_over_le_fppfTopology_over`), so an fppf sheaf on `Over S` restricts to an `IsZariskiSheaf` on any open-local test category (`LocalRepresentability.isZariskiSheaf_comp_ι_of_isSheaf_fppfTopology_over`). [CommGrpObj](Sites/OverRepresentability/CommGrpObj.lean): the group law of a representing scheme: for `S` locally Noetherian and `F : (Over S)ᵒᵖ ⥤ AddCommGrpCat` represented on locally Noetherian test schemes by `P` locally of finite type, `P` is a commutative group object of `Over S` and the representation is additive on points (`Scheme.LocallyNoetherianOver.commGrpObjOfRepresentableBy`, `homEquiv_mul`, `homAddEquiv`; Stacks 022S). |
| [Fppf covering points](Sites/FppfCoveringPoints.lean) | A covering sieve of `Scheme.fppfTopology` contains, through every point, a flat morphism locally of finite presentation (`Scheme.exists_flat_mem_range_of_mem_fppfTopology`, by induction on the generation from `Scheme.fppfPrecoverage`), and likewise for `Scheme.fppfTopology.over S` (`Scheme.exists_flat_mem_range_of_mem_fppfTopology_over`); Mathlib imports only. Consumer: [Picard/FiberCondition](Picard/FiberCondition/Subsheaf.lean) |
| [Fppf quotient representability](Sites/FppfQuotient.lean) | Kleiman's Lemma 4.9 in fppf form on locally Noetherian test schemes (arXiv:math/0504020v1, p. 30): for an fppf sheaf `F` on `Over S`, a subfunctor `G` of its restriction to `Scheme.LocallyNoetherianOver S`, `z ∈ G(Z)` and a flat surjective `q : Z ⟶ Q` locally of finite presentation with `R = Z ×_Q Z` on locally Noetherian points ((h₁), (h₂)), `G`-sections lifting fppf-locally to `Z` ((h₃)) and `G` descending along `q`, the unique `λ ∈ F(Q)` with `q^* λ = z` (`Scheme.fppfQuotientSection`) makes `Q` represent `G` (`Scheme.representableByOfFppfQuotient`). Coverings: `Scheme.ofArrows_mem_fppfTopology_over`. Mathlib imports and `LocallyNoetherianOver` only |
| [FlatteningStratification](FlatteningStratification/README.md) | Rank strata of a quasi-coherent sheaf of finite type, cut out by Fitting ideal sheaves, with their universal property (the case `n = 0` of the flattening stratification) |
| [Morphisms](Morphisms/README.md) | Etale stalk/neighborhood comparison, finite field-valued lift sets, finite-etale objects and base change, section rigidity, smooth regularity/dimension and proper graph modifications |
| [Properties](Properties/README.md) | Normal/domain stalks, component openness, connected integrality, qcqs affine induction and finite dense-affine covers |
| [Stalk](Stalk/README.md) | Actual stalk-map, flat-base-change, polynomial, generic-fibre and dimension comparisons |
| [Geometrically](Geometrically/README.md) | Geometric connectedness under field extension, algebraic-closure detection and proper geometrically integral constants |
| [Group](Group/README.md) | Actual group-object pullback, canonical identity/composition and multiplicative point-fibre comparison |
| [Curves](Curves/README.md) | Native field curves, divisors, degree, Riemann--Roch and projective-line comparisons, with explicit hypotheses and remaining representability inputs |
| [AlgebraicSimplex](AlgebraicSimplex/README.md) | Literal coordinate quotients, face maps, field coefficient extension and finite scalar dependence |
| [Grassmannian](Grassmannian/README.md) | Coordinate charts, overlaps and glued schemes representing the affine Grassmannian functor and its natural-transformation extension |
| [HilbertScheme](HilbertScheme/README.md) | The Hilbert functor of `P^n_A`, Mumford's uniform regularity bound, direct images of flat families, the Grassmannian point and its naturality on Noetherian affine test schemes, and the flattening-stratum image step, the Hilbert scheme of `P^n_A` over a Noetherian base and the open subscheme representing the families contained in an open `U ⊆ P^n_A` |
| [Picard](Picard/README.md) | Relative group presheaves, normalized and rigidified comparisons, and fppf sheafification; Picard representability remains open |
| [FunctionField](FunctionField/README.md) | Canonical generic inclusions, dominant field maps, generic-fibre isomorphisms and extension to targets integral over the base |
| [Generic finite-etale normalization](Normalization/GenericFiniteEtale/README.md) | Actual relative normalization and generic recovery, with separate normal/locally Noetherian finiteness and stalk conclusions |
| [BaseChange](BaseChange/README.md) | Scheme-valued coefficient pullbacks with original projections and naturality |
| [Spec](Spec/README.md) and [Products](Products/README.md) | Polynomial/Laurent spectra, coordinates and zero section, localization squares and integer-base product diagrams |
| [Limits](Limits/README.md) | Finite native over-products and arbitrary base-change comparisons |
| [IdealSheaf](IdealSheaf/README.md) | Actual kernel ideal modules, restrictions and canonical quotient-flat base-change maps |
| [EffectiveCartierDivisor](EffectiveCartierDivisor/README.md) | Finite presentation of invertible closed ideals and smooth relative-dimension-one Cartier criteria |
| [ProjectiveSpace](ProjectiveSpace/README.md) | Actual polynomial Proj, charts, twists, finite presentations, affine immersions, base change and chartwise Euler sequences |
| [Cohomology](Cohomology/README.md) | Actual Zariski `Sheaf.H`, structural scalars, Cech and derived comparisons, qcqs flat base change, proper coherent finiteness, [field Hilbert polynomials](Cohomology/Projective/HilbertPolynomial/README.md), projective regularity and [relative projective duality](Cohomology/Duality/Projective/Relative/README.md) with its stated base hypotheses |
| [EtaleCohomology](EtaleCohomology/README.md) | Actual small-etale H1, coefficient and torsor maps, finite locally constant comparisons and scheme-specific Kummer constructions |

Lower [commutative algebra](../RingTheory/README.md), [categorical structure](../CategoryTheory/README.md), [homology](../Algebra/Homology/README.md) and [topological sheaves](../Topology/Sheaves/README.md) supply the reusable prerequisites. [Root reading routes](../../docs/README.md) explain their interfaces. Reusable curve, projective-line, genus and degree theory is admitted by the full R5 migration; arithmetic markings, literal Tate analytic realization and Quillen K/G/Q/S applications retain downstream owners.

The [closed-immersion](Morphisms/ClosedImmersion/ComponentStalk.lean) and
[principal base-change](Stalk/PrincipalBaseChange.lean) leaves concern actual
stalk kernels. Their component and uniformizer applications keep the literal
closed immersion, pullback projection and structural scalar map.

The Grassmannian leaves retain `BaseChangeMkQFormula`; the focused
[formula supplier](../RingTheory/Grassmannian/BaseChangeFormula.lean) proves it
for every commutative ring and module. The interpretation on nonaffine tests
as locally free module-sheaf quotients remains separate.

Godement and derived interfaces retain their bounds and original unit equations.
Proper coherent finiteness and smooth differential rank have proved suppliers;
the full arbitrary-base `LocalFreeCohomologyBaseChange` family remains an explicit
input, with the exact conditions recorded in [INTERFACES.md](../../docs/INTERFACES.md).

Focused interface guides: [Finite correspondences on the two-dimensional torus](Torus/FiniteCorrespondence/README.md).

The [surface families](Surfaces/README.md) also use original-map
[finite function-field normalization](Normalization/FiniteFunctionField.md).
For an integral scheme and a specified finite extension of its actual
function field, finiteness and local Noetherianity retain the required
Nagata finite-type chart hypotheses. The construction uses the original
generic map and makes no finite-flat or finite-étale assertion.
The [cohomology](Cohomology/README.md), [duality](Cohomology/Duality/Projective/Relative/README.md)
and [descent](Descent/README.md) guides describe the completed prerequisites
and their conditions; general singular-surface resolution remains open.
