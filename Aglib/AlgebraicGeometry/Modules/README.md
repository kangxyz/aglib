# Actual structure-module sheaves

Objects are Mathlib's actual `X.Modules` on a scheme's Zariski site. Native `Scheme.Modules` functors carry the structure-ring scalar maps. Project extensions use `AlgebraicGeometry.Scheme.Modules` and mathematical subnamespaces.

[Stalk](Stalk/Basic.lean) constructs `moduleStalk`, `moduleStalkMap` and the actual stalk/skyscraper adjunction; `moduleStalkExactFunctor` is the genuine module-valued stalk exact functor. [Support](Support.lean) defines support through nonzero stalks, gives `isZero_iff_stalks` and compares support with actual open restriction. [Exact](Exact.lean) supplies `sheafExactStructure`, exact open restriction and the supported-away property. [Epimorphisms](../../Algebra/Category/ModuleCat/Sheaf/Epimorphisms.lean) proves actual sheaf epimorphisms are locally surjective. [IsomorphismFunctors](IsomorphismFunctors.lean) gives pullback/direct-image equivalences for scheme isomorphisms.

[Ext](Ext.lean) gives the standard `Type (u + 1)` native Ext universe for
`X.Modules`, including its unfolded `SheafOfModules` form. It specializes
the lower ringed-site theorem without a resizing or geometric finiteness
hypothesis.

[Linear](Linear.lean) defines `globalScalarCenter` and
`globalScalarEndomorphism` by original global-function multiplication on
each open. On the structure module this is the original `unitMul`.
`moduleCategoryLinearOfHom X α` is the native `Linear R X.Modules` structure
for a specified map to global functions; it remains explicit to distinguish
different structural maps. Its sectionwise formulas retain the original
restriction and module action. Ring and scheme universes may differ.
`unitHomGlobalSectionsLinearEquivOfHom X α M` identifies morphisms from the
structure module with the global sections `M(⊤)`, linearly over `α` (with
`Module.compHom` on `M(⊤)`); the forward map is evaluation on one. Its
consumer is Nitsure's Lemma 3.2 through
[ProjectiveSpace/Tensor/Equivalence/Hom](../ProjectiveSpace/Tensor/Equivalence/Hom.lean).

[InternalHom](InternalHom.lean) is the generic `Scheme.Modules.InternalHom` of actual structure-linear maps between restrictions. Its `sectionHomEquiv` identifies sections with the actual restricted module-sheaf morphisms. It lies below invertible sheaves and has no rank-one hypothesis. The
[restriction and gluing guide](InternalHom/README.md) gives literal native
open-restriction comparisons and unique global module morphisms from
compatible arrows on jointly covering open immersions. It needs no
quasicoherence or finiteness, allows independent cover-index universes and
includes empty covers on empty schemes. Euler maps and higher-direct-image
base-change maps share this lower interface.

| Subfamily | Objects and principal results |
| --- | --- |
| [Generators](Generators/README.md) and [Locality](Locality/README.md) | Actual open-free generators, finite local lifts and stalk/open-cover detection |
| [Restriction](Restriction/README.md), [Pullback](Pullback/README.md), [Pushforward](Pushforward/README.md) | Canonical geometric functors, units/counits, extension by zero and scalar comparisons |
| [Complex](Complex/README.md) | Ordinary integer complexes, geometric restriction, flat pullback, tensor and acyclicity on specified opens |
| [PerfectComplexes](PerfectComplexes/README.md) | Strict term-bounded finite locally free complexes, their inherited exact structure, locally strict derived models and open restriction |
| [StructureSheaf](StructureSheaf/README.md) and [BaseChange](BaseChange/README.md) | Actual direct image of the unit and the adjunction-mate base-change map |
| [QuasiCoherent](QuasiCoherent/README.md) | Affine module comparison, local/limit closure, finite-type objects and scalar-localization results |
| [FinitePresentation](FinitePresentation/README.md) | Actual finite generators/relations, transport and open-locality without a coherent-category dependency |
| [Flat](Flat/README.md) | Genuine stalkwise-flat objects and arbitrary pullback exactness for flat quotients |
| [LocallyFree](LocallyFree/README.md) | Canonical finite local bases, exact arbitrary pullback, proved fibre dimension and rank detection |
| [FittingIdeal](FittingIdeal/README.md) | Fitting ideal sheaves of quasi-coherent sheaves of finite type, their pullback and the local freeness criterion |
| [Coherent](Coherent/README.md) | Locally Noetherian abelian/exact specialization and coherent direct image |
| [Invertible](Invertible/README.md) and [Differentials](Differentials/README.md) | Ordinary Picard tensor/dual/pullback and actual universal differentials/etale comparison |

The main consumers are the more specific object-property categories and [scheme cohomology](../Cohomology/README.md). Scheme/object/coefficient universes remain those of the source statement, including the sheaf-object universe when a small model is used.

The latest general surface adds [Tensor](Tensor/README.md), [Stalk](Stalk/README.md), [ProjectionFormula](ProjectionFormula/README.md), coefficient/cartesian base change and the affine/tensor subfamilies of finite locally free sheaves. All tensors delegate to one site construction. The arbitrary-morphism projection formula requires finite local freeness of its target coefficient; the closed-immersion module formula permits arbitrary coefficients.

The perfect-complex family uses these same ordinary sheaf complexes. `Scheme.Modules.Complex.StrictPerfect X` and `Perfect X` are full subcategories of the chain-map category; the latter's local-model predicate uses the canonical `DerivedCategory.Q`. The [family guide](PerfectComplexes/README.md) separates term bounds, local derived representatives and the exact structures actually supplied. Its definitions and restriction results hold on arbitrary schemes, without global quasi-compactness, Noetherianity or projectivity assumptions.

[KernelSections](KernelSections.lean) identifies sections of the original sheaf kernel with the kernel
of the original section map on every open. Its native evaluation comparison
retains the original kernel inclusion, without an affine hypothesis.

[ZeroLocus/ImageFactorisation](ZeroLocus/ImageFactorisation.lean): for `φ : M ⟶ 𝒪` with
`Hom.ImageIdealLocalizes φ` (for instance quasi-coherent `M`), the factor onto the image ideal is an
epimorphism (`Hom.epi_zeroIdealFactor`), the factorisation is an image
(`Hom.zeroIdealMonoFactorisationIsImage`), and the image ideal is determined by any
epimorphism–ideal-inclusion factorisation (`Hom.imageIdealData_eq_of_epi_comp`); for quasi-coherent
`M`, `φ` vanishes on `𝒪_X / I(φ)` (`Hom.comp_toQuotientModule_imageIdealData_eq_zero`).
[ZeroLocus/Pullback](ZeroLocus/Pullback.lean): `I(f^* φ) = I(φ).comap f` for quasi-coherent `M` and
every `f`, without flatness (`Hom.imageIdealData_pullback`, Stacks Tags 01JU, 01AJ); main's
`Hom.imageIdealData_restrict` ([ZeroLocus/Restriction](ZeroLocus/Restriction.lean)) is the
restriction-functor form for open immersions.

[ZeroLocus/LocallyFree](ZeroLocus/LocallyFree.lean): the zero scheme of `σ : F ⟶ E`, for `F`
quasi-coherent and `E` finite locally free of constant rank `d` (`SheafHasRank E d`), is
`Hom.zeroLocusIdeal σ d = Fitt_{d-1}(coker σ)` (`Fitt_{-1} = 0`). A morphism `g : T ⟶ X` from any
scheme factors through it iff `g^* σ = 0` (`Hom.exists_lift_zeroLocusSchemeι_iff`), it pulls back
to the zero scheme of `f^* σ` (`Hom.zeroLocusIdeal_comap`), and it is `X` iff `σ = 0`. For
sections `s i : 𝒪_X ⟶ E` (any index type) the zero scheme of `freeDesc s : 𝒪_X^{(I)} ⟶ E`
represents the vanishing of all pulled-back sections, also as elements of `Γ(T, g^* E)`
(`exists_lift_zeroLocusSchemeι_freeDesc_iff`, `…_globalSections`), and pulls back to the zero
scheme of the pulled-back sections (`zeroLocusIdeal_freeDesc_comap`). Stacks Tag 0FA8 (definition
through `E^∨`, Section 42.44); invertible case Tags 02OQ, 02OR. Varying rank is not covered.
For `E = 𝒪_X` it is the image-ideal zero scheme (`Hom.zeroLocusIdeal_one_eq_imageIdealData`).
`IdealSheafData.eq_of_forall_comap_eq_bot_iff` (a closed subscheme is determined by the morphisms
factoring through it) and `pullback_map_comp_eq_zero_iff` are relocation candidates for new sibling
leaves under `IdealSheaf/` and `Modules/Pullback/` (not the widely imported
`IdealSheaf/LocallyClosed`).

[ZeroLocus/Order](ZeroLocus/Order.lean): for closed subschemes `W ≤ W'`, `I_W ⟶ 𝒪 ⟶ 𝒪/I_{W'}`
vanishes (`IdealSheafData.idealInclusion_comp_toQuotientModule_eq_zero_of_le`); a module-to-unit
map whose image ideal lies in `W` vanishes on `𝒪/I_W`
(`Hom.comp_toQuotientModule_eq_zero_of_imageIdealData_le`, quasi-coherent source, generalizing
`Hom.comp_toQuotientModule_imageIdealData_eq_zero`); image ideals shrink under precomposition
(`Hom.imageIdealData_comp_le`); the image ideal vanishes iff the map does
(`Hom.imageIdealData_eq_bot_iff`).
