# Etale cohomology

This family owns scheme-specific cohomology of the actual small-etale site.
Its principal declaration namespace is
`AlgebraicGeometry.Scheme.EtaleCohomology`. It is a sibling of the
[Zariski/module-cohomology family](../Cohomology/README.md).

| Subfamily | Existing objects, maps and conditions |
| --- | --- |
| [Original module cohomology](Coefficients/Cohomology.lean), [derived comparison](Coefficients/DerivedCohomology.lean), [derived slices](Coefficients/DerivedSliceCohomology.lean) and [slice cohomology](Cohomology/SliceComparison.lean) | Actual small-etale realizations of the generic site comparisons, with their original scalar, section, unit and universe data. The scheme adapters are owned here; the general constructions remain in the site and homological families. |
| [H1](H1/README.md) | Actual `Sheaf.H L 1`, coefficient maps, exact inverse image, direct image, canonical transports, torsors and finite-etale representation |
| [H0 proper henselian](H0/README.md) | Original constant-finite sections and `Sheaf.H` degree-zero pullbacks are bijective over any proper henselian local base; sections extend to actual finite locally constant coefficients. |
| [H1 finite constant](H1/ConstantFinite/README.md) | Original `H1Etale` closed-residue pullback is bijective for every finite constant additive group, with no order-invertibility or Noetherian premise; the result extends to actual finite locally constant abelian sheaves. |
| [Constructible coefficients](Constructible/README.md) | Affine-local finite constructible locally closed partitions with original FLC restrictions define constructibility on any scheme. Such coefficients have finite original geometric stalks and are internally torsion. On qcqs schemes, an actual finite locally closed cover is constructed; its pieces may overlap. On a qcqs scheme, a positive integer annihilating the original scalar identity is constructed. |
| [Finite locally constant and presented coefficients](Constructible/README.md) | The original generic adjunction unit is monic for every finite locally constant coefficient on an integral scheme, and such coefficients have actual finite Galois constant trivializations over fields. On a qcqs base, [actual finite local constancy](Constructible/FiniteLocallyConstantCompactness.lean) gives ordinary `IsFinitelyPresentable.{u+1}` with no supplied presentation. The separate explicit finite-`ZMod` presentation supplier retains its presentation data; existence of those presentations remains open. |
| [Connected FLC cogenerators](Constructible/FiniteCogenerators/LocallyConstant.lean) | On a connected scheme, an actual FLC coefficient embeds by the original adjunction unit and a produced trivialization into the finite direct image of an actual finite constant sheaf. The finite étale surjection and finite value at universe `u+1` are constructed. The separate original-unit monomorphism theorem retains FLC and flat surjective pullback on arbitrary schemes. |
| [Normal constants](Constructible/NormalConstants.lean) | For integral `X` whose local rings are integrally closed and finite `A`, the original generic-point unit induces `constantGenericIso` from the constant sheaf on `X` to direct image of the constant sheaf on `Spec(X.functionField)`. This uses the original adjunction unit and inverse-image constant-coefficient map; it assumes no Noetherian, Nagata, excellence, quasi-compactness, invertible-order, properness or strict-henselization premise. It is a finite-constant comparison input, not finite cogeneration or proper base change. |
| [FiniteLocallyConstant](FiniteLocallyConstant/CoefficientSquare.lean) | Coefficient, section and pullback comparisons with the original local-trivialization and comparison premises |
| [Kummer](Kummer/Coefficients.lean) | Actual root coefficients, power-fibre torsors and field/stalk comparison maps with their stated level and representation hypotheses |
| [Derived cohomology](Derived/BaseChange.lean) | Original all-degree pullback, bounded-below `D+` exchange, and ordinary, derived and higher identity/pasting equations through the native comparisons. The finite subfamily supplies exchange invertibility for finite morphisms; general proper base change and unbounded scope remain open. |
| [Continuity](Continuity/README.md) | Original all-degree fixed-qcqs coefficient continuity and varying-system qcqs scheme-limit continuity with affine transitions. The latter constructs the former section/cone inputs, retaining actual limit, independent Ext and group-colimit premises. |
| [Finite direct image and base change](Finite/README.md) | For an arbitrary finite morphism, original direct image on `AbelianSheaf.{u,u+1}` preserves epimorphisms, homology and finite colimits, and positive higher direct images vanish. The canonical ordinary, `D+` and all-degree higher exchange maps are invertible for actual cartesian squares over arbitrary schemes, retaining the displayed derived-category universes. [Original cohomology](Finite/Cohomology.lean) identifies cohomology of finite direct image with source cohomology by actual pullback and counit. |
| [Original cohomology and higher-image stalks](Stalk/README.md) | Original presheaf sheafification and germs; marked strict-local limit cohomology computes the actual higher-image stalk, with coefficient naturality, every pointed-neighborhood leg and original q0 normalization. Actual chart/Ext/colimit premises remain. |
| [Field cohomology](Fields/README.md) | Over algebraic extensions of `k(t)` with separably closed `k`, original degrees `q ≥ 2` vanish for genuine finite `p`-killed FLC coefficients when `p` is prime and invertible, and for cyclic/root coefficients of positive invertible order. Arbitrary purely inseparable root comparison is supplied; higher Gm vanishing is not asserted. |
| [Strictly local curve comparison](Curves/README.md) | The original finite-constant closed-fibre restriction is surjective in every natural degree for every finite scheme over native `P1_R`, with `R` henselian local and separably closed residue, finite abelian values and independent Ext universes. No Noetherian/excellence/completeness/flatness/fp/normality/order premise or higher injectivity claim is added. |
| [Fibrewise-closed geometric points](GeometricPoints/FibrewiseClosed/README.md) | Under only `LocallyOfFiniteType p`, genuine geometric-point lifts detect covers on every object of the actual small-etale site; the resulting `Point.{u+1}` family detects isomorphisms of `AbelianSheaf.{u,u+1}`. No Ext or proper-base-change theorem is asserted. |
| [Original stalks](GeometricPoints/FibrewiseClosed/README.md) and [inverse image](GeometricPoints/InverseImage/README.md) | The canonical `pointSmallEtale` stalk comparison and original inverse-image `stalkUnit` isomorphism hold for every standard-value abelian sheaf; only the separate fibrewise-closed detection consumer needs `LocallyOfFiniteType p`. |

Use focused imports, for example:

```lean
import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Pullback

open AlgebraicGeometry.Scheme.EtaleCohomology
```

`AbelianSheaf` uses the actual small-etale topology and `H1Etale` is original
Mathlib `Sheaf.H` in degree one. Keep displayed `HasSheafify`/`HasExt`
universes, markings, point data and theorem-family premises. General torsor
classification and finite representation do not impose an invertible group
order; the separate finite-coefficient package retains its positive globally
invertible level. Kummer and field-comparison leaves keep their own hypotheses.

Generic site, Ext and derived-category constructions remain in their lower
mathematical owners. Finite-etale cover geometry remains in
`AlgebraicGeometry/Morphisms/FiniteEtale`. The Kummer leaves that extend
`GroupCohomology.Kummer` keep that native object namespace; the directory
change does not duplicate their group-cohomological objects.

The [older migration guide](../../../docs/ETALE_COHOMOLOGY_MIGRATION.md)
records the module relocation and namespace change. The
[foundation note](../../../docs/migration/etale-foundations-2026-10-23.md)
describes the generic and derived providers.

The canonical exchange maps retain their degree-zero normalization.
`h1Pullback_square` keeps its four displayed `HasExt` universes;
`derivedBaseChangeMap_h1_square` compares the actual derived mate through the
constant-sheaf, adjunction, shift and single comparisons. The ordinary
`baseChangeMap_hComp`, `_vComp` and `_vId` equations use the original
inverse-image and direct-image composition maps. Their derived counterparts
use the native `D+` adjunctions and displayed derived-category instances.
For every natural degree, `higherBaseChangeMap_hComp`, `_vComp` and
`_vId` retain the actual higher-image comparisons and homology of the
composite derived images. The higher vertical identity retains its native
comparison, without identifying a positive-degree derived image of an identity
with the identity functor.

Invertibility is supplied by the
[ordinary étale-chart comparison](Stalk/EtaleDirectImageMate.lean) for arbitrary
vertical morphisms and étale horizontal morphisms, and by the
[finite subfamily](Finite/README.md) for finite vertical morphisms and arbitrary
horizontal morphisms. The general proper-base-change theorem and unbounded
derived scope remain open. The basic interfaces are
[DirectImage](DirectImage.lean), [Pullback](Pullback.lean),
[PullbackComposition](PullbackComposition.lean),
[BaseChangeMap](BaseChangeMap.lean) and
[Derived base change](Derived/BaseChange.lean).

## Further small-etale inputs

| Input | Scope and owner |
| --- | --- |
| [Strictly local](StrictlyLocal/README.md) | For henselian local rings with separably closed residue field: arbitrary jointly surjective étale families split, terminal covering sieves are maximal, and original positive-degree `Sheaf.H` vanishes for arbitrary value and Ext universes under native existence assumptions. These are suppliers, not a proper-base-change theorem. |
| [Artin–Schreier](ArtinSchreier/README.md) | The actual additive small-etale short exact sequence and original constant-prime-field/native-kernel isomorphism are supplied for every scheme `X : Scheme.{u}` when `p` is prime and `(p : Γ(X, ⊤)) = 0`, including empty schemes, with coefficients in `AddCommGrpCat.{u+1}` and no extra affine, Noetherian, exact-characteristic or Ext premise. The finite-etale root cover and its lower finite/free algebra remain linked inputs. This is not affine-etale acyclicity or proper base change. |
| [Binary-form product](../ProjectiveSpace/BinaryFormProduct/README.md) | The actual finite surjective map to projective space has a cartesian coefficient-map square under every commutative-ring map and every degree `n`, including zero. This is an available projective geometric input, not a proper-base-change theorem. |
| [Amitsur module complex](../../Algebra/Homology/Amitsur/README.md) | Under faithfully flat scalar extension, the actual augmented module Amitsur complex is exact in every degree and the unaugmented complex has zero positive homology for arbitrary coefficient modules. This is algebraic module exactness, not étale-sheaf acyclicity. |
| [Torsion sheaves](Torsion/README.md) | On the actual small-etale site, internal torsion is detected by original geometric stalks and every torsion sheaf is the actual filtered colimit of its native factorial annihilator kernels. This does not assert cohomological continuity or proper base change. |
| [Torsion comparison](Torsion/README.md) | The general original-cohomology comparison reduces internally torsion coefficients to genuine prime `ZMod` module-sheaf tests, assuming sequential-colimit preservation in each degree. [QcqsComparison](Torsion/QcqsComparison.lean) supplies that continuity for morphisms between qcqs schemes, leaving only the all-degree prime-module comparison as an application hypothesis. Independent source/target Ext universes are retained. |
| [Surjectivity tests](Torsion/SurjectivityCriterion.lean) | For all moduli, including zero and one, degree-zero injectivity and surjectivity in every degree below `q`, tested on every genuine module coefficient, give injectivity of the original pullback in degree `q`. On qcqs source and target, prime-module degree-zero injectivity and all-degree surjectivity suffice for every internally torsion coefficient, retaining independent Ext universes. |
| [Exact-map local criterion](../../Algebra/Homology/DerivedCategory/Ext/CogeneratorComparison.lean) | Actual per-object coefficient colimits with stages in `P`, and monomorphisms from `P` into `T`, reduce original comparison to all-degree test surjectivity, source Ext acyclicity of injective coefficient images, degree-zero injectivity and target preservation of those colimits. Moving the degree-zero injectivity test to `T` also requires both degree-zero preservation conditions and monomorphism preservation by colimits in the common value universe. |
| [Constant-ring module bridge](../../Algebra/Category/ModuleCat/Sheaf/ConstantRing/Basic.lean) and [genuine ZMod specialization](../../CategoryTheory/Sites/Torsion/ZMod/Ringed.lean) | Under the stated native sheafification hypotheses, module-valued sheaves over an arbitrary ring identify with modules over its actual constant ring sheaf, retaining the original underlying sheaf. The genuine `ZMod n` specialization includes modulus zero. This interface compares coefficient categories. |
| [ZMod underlying cohomology](Torsion/ZModCohomology.lean) | On any scheme and for every modulus, including zero and one, the original underlying functor on genuine module sheaves preserves finite limits and colimits. An injective genuine module sheaf has zero positive original underlying abelian cohomology, with an independently supplied Ext universe or the native standard Ext endpoint. |
| [Module-injective pullback criterion](Torsion/InjectiveCriterion.lean) | Original pullback comparison for ringed module coefficients is conditional on degree-zero comparison and positive cohomology vanishing for the actual pulled-back underlying injective module sheaves, with independent module/source/target Ext universes. |

The qcqs theorem supplies sequential coefficient continuity. Prime-module
degree-zero injectivity and all-degree surjectivity remain test hypotheses.
The exact-map local criterion consumes actual colimit presentations and
monomorphism embeddings. Bounded genuine coefficients have original filtered
presentations with geometrically constructible, ambient-FP stages on
separated schemes; ambient FP also holds on every original affine open.
Finite constant cogeneration is proved on affine Noetherian schemes, and
its nonaffine global extension remains separate. The constant direct-image
sheaf cocone bridge is proved. Actual projective-line local comparison and
general proper-base-change assembly remain applications; no conditional
reduction alone closes them.

## Multiplicative and curve inputs

| Input | Objects, maps and conditions |
| --- | --- |
| [Artin sheaf equivalence](Artin/SheafEquivalence.lean) | For locally Artinian quasi-separated source and target, a surjective morphism whose actual finite-etale base-change functor is an equivalence makes the original direct and inverse image functors equivalences. [Root-cohomology pullback](Kummer/ArtinPullback.lean) is then bijective for positive globally invertible levels. [Nilpotent quotients](Kummer/ArtinNilpotent.lean) of Artinian rings and [residue maps](Kummer/ArtinResidue.lean) of Artinian local rings supply concrete cases. |
| [Picard and Kummer](Picard/KummerQuotient.lean) | For positive `n` invertible in global sections, the literal `picardQuotientBoundary` embeds ordinary Picard classes modulo `n` into original `Sheaf.H (mu X n) 2`, naturally for the ordinary Picard and root-cohomology pullbacks. [Surjectivity of the Kummer boundary](Kummer/CohomologyConsequences.lean) from degree `q` retains power injectivity in degree `q + 1`; vanishing of `Sheaf.H (mu X n) (q + 1)` retains power surjectivity in degree `q` and injectivity in degree `q + 1`. |
| [Derived divisibility](Derived/OriginalDivisibility.lean) | Bijectivity of multiplication by `n` on source cohomology in degrees `q` and `q + 1`, together with invertibility of multiplication by `n` on every positive higher direct image, gives bijectivity on degree `q + 1` cohomology of the direct-image coefficient. The source and target Ext and derived-category inputs remain independent. |
| [Quasicoherent cohomology](QuasiCoherent/README.md) | Actual additive coefficients use original pullback-module sections and geometric-unit restrictions. Arbitrary modules have positive affine étale acyclicity, and original Zariski/module cohomology compares with étale cohomology in every degree on every scheme, with independent Ext universes and additive naturality. No coefficient flatness, finite generation, qcqs or Noetherian hypothesis is added to the global comparison. |
| [Tsen](../../FieldTheory/Tsen/AlgebraicFunctionField.lean), [Brauer splitting](../../FieldTheory/Brauer/C1Splitting.lean) and [cocycle primitives](../../FieldTheory/Brauer/C1Cocycles.lean) | Every algebraic extension of `K(T)` with algebraically closed `K` is C₁. Over an infinite C₁ field, native central simple algebras split and finite-Galois multiplicative two-cocycles have actual primitives. [Amitsur unit primitives](../../FieldTheory/Galois/AmitsurPrimitives.lean) use the original conerve rings and cofaces for finite Galois extensions of those algebraic function fields. |

The [strictly local curve endpoint](Curves/StrictlyLocalComparison.md) now
gives all-degree finite-constant surjectivity through the original map.
The field theorems retain their prime or positive-invertible-order conditions;
they do not claim higher Gm vanishing or invariance. General torsion proper
base change and the unbounded six-operation assembly remain open.

## Original geometric stalks and inverse images

[StalkUniverse](GeometricPoints/StalkUniverse.lean) compares the canonical
`FibrewiseClosed.largePoint η` sheaf fibre with the original
`pointSmallEtale η` fibre for every actual `AbelianSheaf.{u,u+1}`. The
isomorphism uses the literal lifted Hom witness and is natural for every
coefficient morphism. The comparison itself requires no finite-local-constant,
Ext, or `LocallyOfFiniteType` premise.

[InverseImage](GeometricPoints/InverseImage/README.md) proves that for every
morphism `f : S ⟶ X`, geometric point `η : Spec Ω ⟶ S`, and actual
`L : AbelianSheaf.{u,u+1} X`, the original `stalkUnit f η L` is an isomorphism.
Its natural-isomorphism component is definitionally that original map, and the
germ formula retains the original section and `pulledBackPoint`. It is natural
in coefficient maps and agrees with the existing represented-coefficient
isomorphism when a representation is supplied. No FLC, Ext, or
`LocallyOfFiniteType` condition is required for this stalk comparison. General
inverse-image stalk-unit bijectivity at wider coefficient universes remains
outside scope; no proper-base-change theorem is asserted.

The separate detection consumer
`isIso_of_original_geometricStalks` continues to require
`[LocallyOfFiniteType p]`. That geometric condition belongs to the
isomorphism-detection theorem, not to the stalk-unit comparison.

## Further coefficient and six-operation suppliers

[Constructible module coefficients](Constructible/Modules/README.md) retain
finite generation over an independent-universe commutative coefficient ring.
They include arbitrary inverse image, actual etale-cover descent, Noetherian-ring
kernel/cokernel/extension closure, and finite-etale direct-image constructibility.
Their underlying additive groups need not be finite. These results do not
supply descent of native finite coefficient diagrams to Noetherian models.

[Finiteness](Finiteness/README.md) includes characteristic-primary proper
cohomology and invertible-order smooth proper curve H1, with their displayed
scalar, trivialization and Ext hypotheses. [Smooth base change](SmoothBaseChange/README.md)
supplies unconditional etale exchange and a smooth-to-affine-line reduction;
the actual positive-relative-dimensional affine-line theorem is still an input.

[Exceptional images](Exceptional/README.md) and [localization](Localization/README.md)
use genuine constant-ring module sheaves, their actual lower-shriek counit and
closed-image unit. Exact open extension, localization, native D+ and unbounded
ordinary-image suppliers are available. Proper-refinement invertibility,
compactification independence and a complete exceptional-image calculus remain
open. The coefficient equivalence with module-valued sheaves retains the
original units; it is not a definitional identification of the two carriers.

The [source integration note](../../../docs/migration/etale-six-functor-suppliers-2026-10-24.md)
records admitted families, excluded drafts, deduplication and exact boundaries.
