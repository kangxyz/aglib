# Native mathematical interfaces

`Aglib` is an import root. Mathematical declarations extend native owners: `Module` and `Algebra` for algebraic objects/maps, `CategoryTheory` for categorical structure, `TopCat.Sheaf` for topological sheaves, and `AlgebraicGeometry.Scheme`/`Scheme.Modules`/`Scheme.Cohomology` for scheme-specialized objects. A declaration namespace need not be its source module path.

The selected exact-category structure lives in `CategoryTheory.ExactCategory`. Its `ExactFunctor` preserves chosen conflations and is distinct from other native exact-functor notions. Site Cech declarations use `CategoryTheory.Cech`; small-model declarations use the actual `CategoryTheory.SmallModel` interface. [namespace-map.json](namespace-map.json) records correspondence and [module-map.json](module-map.json) records path changes. Original names are provenance; downstream adapters belong in the original packages.

## Object properties and categorical structures

Ambient module sheaves are Mathlib's actual `X.Modules`. Quasicoherence, finite type, finite presentation and finite local freeness are distinct properties of these sheaves. The locally Noetherian coherent category is an abelian/exact specialization; those categorical structures must not impose local Noetherianity on lower finite-type or finite-presentation constructions that do not need it.

Affine comparison relates actual finite-type quasicoherent sheaves to finite modules. Arbitrary pullback preserves finite presentations and coherent objects under the source interfaces' hypotheses; flatness supplies the exact coherent-pullback interface. Finite and closed-immersion pushforward keeps its actual affine scalar-restriction/quotient comparison. Vector bundles use finite local bases and arbitrary exact pullback through local splitting.

Small-model construction retains the supplied `EssentiallySmall.{w}` witness and chosen universe `w`. Supplied injective-resolution kernel sequences do not assert existence of resolutions in arbitrary categories. Ext and total-complex comparisons retain their object, morphism and coefficient universes.

## Canonical maps and cohomology objects

The module-base-change map is the actual pullback/pushforward counit mate, with source `g* f_* M` and target the direct image of the pulled-back module on the fibre product. Relative evaluation is the original adjunction counit. The invertibility theorem must concern that constructed map.

Structure and module cohomology are actual additive `Sheaf.H`. For schemes/fields in universe `u`, these Ext-defined types are in `Type (u+1)`. Structural constants induce the field action. The H0 comparison, coefficient maps, connecting maps, geometric pullback and field-tensor map preserve these objects and actions. A resolution/Cech computation becomes a statement about `Sheaf.H` through its proved canonical comparison.

The affine module-base-change theorem now has the unconditional supplier
`Scheme.Modules.affineModuleBaseChange` in
`Aglib.AlgebraicGeometry.Modules.BaseChange.Affine`.
`moduleBaseChangeMap_isIso` concerns the original counit mate for affine `f`,
quasicoherent coefficients and arbitrary `g`; it has no flatness, finiteness or
Noetherian premise. The retained `AffineModuleBaseChange` proposition and older
parameterized consumers remain available, with this proof as their input.

An arbitrary structural ring map `α : R →+* Γ(X, ⊤)` acts on the unchanged
`Sheaf.H` through `moduleCohomologyModuleOfHom`. This action is explicit in `α`
to distinguish different structural maps. The general Cech linear computation
and geometric module-coefficient maps preserve that action and the original
degree-zero comparison. Their construction does not assume flatness or finite
generation. For a quasi-compact separated `f : X ⟶ Spec A`, a flat ring map
`A → B` and any quasicoherent module coefficient, the
[general module base-change supplier](../Aglib/AlgebraicGeometry/Cohomology/BaseChange/Modules/Separated.lean)
now proves invertibility of the original `moduleCohomologyBaseChangeMap` in
every nonnegative degree. Its unit-pure-tensor formula is the actual geometric
cohomology pullback. The [qcqs supplier](../Aglib/AlgebraicGeometry/Cohomology/BaseChange/Modules/Qcqs.lean)
extends this to quasi-compact quasi-separated `f` in every degree, and to
an arbitrary supplied Cartesian square over the same ring map, with the
original unit and tensor mate. Arbitrary-base higher-direct-image and
derived formulations remain separate obligations.

Original module-linear Ext from the structure module now computes the same
additive cohomology in every degree, linearly for the specified structural
ring map. The forward map is native exact scalar forgetting and the original
integer-generator-one map. Coefficient maps, Yoneda composition and degree-zero
section evaluation are explicit. The native long exact sequence and its
Noetherian finite-generation transfers use the same original objects; the
existing field-linear exactness interfaces specialize this implementation.

On actual polynomial projective space over an arbitrary commutative ring,
every integer twist has finite free cohomology in all degrees. Over a
Noetherian base ring, every coherent coefficient has finite cohomology in
every degree, proved from actual finite negative-twist presentations and
coherent kernels. The same conclusion holds through an actual closed
immersion into that projective space, using the original pushforward
cohomology comparison and displayed structural factorization. This does not yet supply the
quantified proper-finiteness family below.

The lower finite-complex numerical interfaces concern the original native
residue-field scalar-extension complexes: their homology dimensions are
upper semicontinuous for finite projective terms, and their native
homological Euler characteristic is locally constant when those terms are
bounded. The latter only requires finitely presented flat terms. A geometric
consumer must supply an actual comparison with its original fibre
cohomology; these statements alone do not discharge a proper base-change
or local-freeness family.

For an actual closed projective embedding over a Noetherian commutative
base and a coherent relatively flat coefficient, the constructed universal
finite-projective model now supplies that geometric comparison. Every
original ordinary fibre-cohomology dimension is upper semicontinuous, and
their intrinsic alternating sum is locally constant. These public endpoints
construct the model internally and retain the original structural actions.
The original degreewise base-change map is identified with the native
homology mate of the same model by a full linear square. Over a reduced
Noetherian affine base, local constancy of an original fibre dimension
gives finite projective original cohomology and arbitrary original base
change. Over a Noetherian local base, the original residue-field
surjectivity criterion gives arbitrary base change and the adjacent-degree
freeness criterion, without reducedness. The actual sheaf-valued `Rf_*` of
this coherent relatively flat coefficient also has a constructed strict
perfect model, both before and after every ring base change. Its
comparison uses the original injective resolution, actual tilde--Gamma
counit and installed derived unit. These projective results do not yet
supply arbitrary perfect-coefficient or general proper endpoints.

The [projective Serre duality family](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/README.md)
proves full complementary-degree coherent Serre duality on polynomial
projective space over a field, including the original Yoneda/residue
pairing, perfectness, coefficient naturality and dimension zero. The top
Hom/cohomology duality also holds over every Noetherian commutative base
ring. Passage to general smooth projective schemes and to general proper
dualizing complexes remains separate.

## Explicit theorem-family inputs

These proposition-valued families quantify over actual objects and constructed maps. They remain parameters of their dependent results.

| Native input owner | Conditions and conclusion |
| --- | --- |
| `AlgebraicGeometry.Scheme.Modules.LocalBasisFibreDimension` | An actual finite local free presentation and a field-valued point in its trivializing open: the fibre is finite and its dimension is the basis cardinality. |
| `AlgebraicGeometry.Scheme.Modules.Differentials.SmoothDifferentialRank` | Smooth field scheme of relative dimension `n`: the actual differential sheaf has rank `n`, over every field. |
| `AlgebraicGeometry.Scheme.Cohomology.ProperModuleCohomologyFinite` | Proper field scheme, finitely presented module sheaf, nonnegative degree: the actual structural-field cohomology is finite-dimensional. |
| `AlgebraicGeometry.Scheme.ProperStructureCohomologyFinite` | Structure-sheaf specialization of proper field-scheme finiteness; the module family supplies it through the actual scalar-compatible comparison. |
| `AlgebraicGeometry.Scheme.ProperGeometricallyIntegralConstants` | Proper geometrically integral field scheme: the actual structural constant map is bijective. |
| `AlgebraicGeometry.Scheme.Cohomology.LocalFreeCohomologyBaseChange` | Proper, locally finitely presented, flat `f`; locally free/finitely presented coefficients; geometric fibre cohomology concentrated in degree zero of rank `r`: direct image has rank `r`, and its actual mate is invertible after every change of base. |

Predicate definitions and theorem suppliers are separate interfaces. Supplier modules in the current source provide smooth regularity/normality/dimension, normal-component openness, etale differential pullback, Noetherian Zariski dimension vanishing, affine module base change and qcqs flat module-cohomology base change over spectra. The local guides name these results and retain their exact conditions. Current elaboration/audit coverage remains in [WORK_PLAN.md](WORK_PLAN.md) and the focused [cohomology plan](COHOMOLOGY_PLAN.md).

## Latest tensor and derived boundaries

The existing [perfect-complex family](../Aglib/AlgebraicGeometry/Modules/Perfect/README.md)
uses actual integer module-sheaf complexes and actual derived isomorphisms.
`strictPerfect` requires bounds on terms and finite local freeness in every
degree. `locallyPerfect` requires strict derived models on neighborhoods;
`HasStrictModel` instead supplies one model over the whole displayed scheme.
Local perfectness gives quasicoherent homology and local cohomological
bounds; quasi-compactness gives one global cohomological bound. It does not
give a global strict model, and this family alone does not prove that a
proper direct image is perfect.

`SheafOfModulesOfCommRing.tensorLeftFunctor`/`tensorFunctor` is the single site tensor. `Scheme.Modules.moduleTensorLeftFunctor`, its right counterpart and invertible wrappers specialize that construction. Finite-locally-free left/right tensor `PreservesHomology` lives in the locally free exactness tier; generic symmetry depends on neither projection formula nor invertible sheaves.

The module projection-formula map is constructed for arbitrary coefficients. Its arbitrary-morphism isomorphism requires finite local freeness of the target coefficient; its closed-immersion module isomorphism does not. The D+ interface retains finite local freeness and its installed derived-unit equation.

`Scheme.Modules.Godement.godementTotal_shortExact` concerns the ordinary integer-complex category and has no boundedness premise. `godementTotalUnit_quasiIso_of_isStrictlyGE`, total homotopy and Plus/derived calculations retain actual lower bounds. Derived direct-image unit invertibility requires termwise flasqueness or the stated jointly covering target opens with flasque pullback restrictions. Flat-base-change unit comparison keeps the actual cartesian square and `Flat j`/`Flat a`; constructing it is not an unconditional base-change isomorphism.

Generic D+ term comparison keeps both lower and upper zero-term bounds. `exactDerivedContractionIso` needs additive `F,G`, homology preservation by `G` and a supplied `F ⋙ G ≅ Id` in the stated abelian/enough-injective/derived setting; only the one-sided derived isomorphism and original unit equation are supplied.

None of these new constructions supplies `ProperModuleCohomologyFinite`, `SmoothDifferentialRank`, `LocalBasisFibreDimension` or `LocalFreeCohomologyBaseChange`. Dependent R5 bridges retain their explicit `hstandard`/family parameters until a supplier is actually introduced and accepted.

The ordinary module-complex layer constructs restriction and pullback on actual integer-indexed complexes. Open restriction preserves homology; pullback preservation retains flatness of the morphism. Left/right coefficient tensor preserves homology when the coefficient is finite locally free. Separately, an actual short exact sequence with finite locally free quotient remains short exact after tensor with an arbitrary coefficient sheaf, by local splitting. Acyclicity on an open means restriction to that displayed open is acyclic; flat pullback uses its actual inverse-image open. These statements need neither a term bound nor a perfect-complex predicate.

The bounded-below geometric pullback/direct-image unit is constructed for arbitrary morphisms. The Godement resolved composite inserts the actual totalization between these functors. Comparison with `derivedFlatPullbackPlus p ⋙ derivedPushforwardPlus p` retains `Flat p` and the canonical derived-category choices. Quasi-isomorphism of the displayed resolved unit and invertibility of the displayed derived unit are the respective inputs to the two transfer theorems; no universal unit-invertibility premise is inferred. Derived open-cover reflection separately assumes each actual local restriction/pullback is invertible, or each local object is zero.

Godement open-unit descent uses an actual cartesian square `IsPullback a b f j` with open immersions `a,j` and a bounded-below target complex. Its final restricted-unit quasi-isomorphism assumes that the displayed local resolved unit for `b` is a quasi-isomorphism. The total-image span uses bounded-below flasque terms; flatness of `f,b` is not a premise of this open descent theorem. This route is distinct from the flat derived-unit transfer.

## Mapping-cone maps

`CochainComplex.mappingCone.map_add` in `Aglib.Algebra.Homology.MappingCone.Map` gives additivity in the two maps of a commutative square of integer-indexed cochain complexes. It assumes only a preadditive category with binary biproducts, with independent object and morphism universes. The [mapping-cone guide](../Aglib/Algebra/Homology/MappingCone/README.md) distinguishes this general map interface from the identity-cone functor's abelian setting.
