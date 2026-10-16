# Finite-projective models for an actual projective embedding

Import `Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel`.
`ProjectiveCohomologyModel R ι i f M n` is actual output data: a native
integer cochain complex, strict term bounds `[0,n]`, finite projective
terms, an actual chain map to the original finite Cech complex of the
pulled coordinate cover, and quasi-isomorphism proofs for this same map
and its original scalar extension after every ring map.

## Constructed supplier

`nonempty_projectiveCohomologyModel_of_embedding` and
`projectiveCohomologyModelOfEmbedding` construct the data from:

- an actual closed immersion `i : X ⟶ ProjectiveSpace R ι`;
- an enumeration `e : ι ≃ Fin (n+1)` and actual factorization
  `i ≫ ProjectiveSpace.toSpec R ι = f`;
- a Noetherian commutative ring `R`;
- actual `affineLocallyFiniteType X M` and actual
  `Scheme.Modules.relativeFlat f M`.

The proof uses the native preimages of the coordinate affine opens,
the actual relative-flat section theorem, the proved universal tensor
tail and bounded flat Cech model, proved embedded-projective coherent
cohomology finiteness, and constructed algebraic finite-projective
replacement. No supplied model or cohomology-comparison family is an
input. The relative flatness concerns the base stalk action, rather than
flatness over the local rings of `X`. Flatness of `f` is not required.

## Original maps and native derived global sections

For a constructed model `D`, `D.toPlus` packs its actual complex in the
native bounded-below category. `D.toCechPlus` is precisely its original
comparison followed by the original good-truncation inclusion.
`D.toCechPlus_quasiIso` proves this literal map is a quasi-isomorphism.

`D.derivedGlobalSectionsIso e I` identifies its native derived image with
the installed `rightDerivedFunctorPlus` of the actual structural-ring
global-sections functor applied to the original coefficient in degree
zero. Here `I` is any actual native module-sheaf injective resolution.
The `_hom` formula retains the actual map to original Cech and the
original module-valued augmentation/injective-resolution comparison.
This object comparison is not inferred merely from homology isomorphisms.

`D.cohomologyLinearEquiv e q` computes unchanged `Sheaf.H` over the
literal structural map of `f`. Its `_apply` formula retains the native
homology map of the actual comparison. Original cohomology carriers stay
in universe `u+1`, while the model modules have carrier universe `u`.

## Every ring base change

For any homomorphism `σ : R →+* B`, `D.baseChangeComparison e hflat σ`
is the original tensor of the actual comparison followed by the original
bounded Cech base-change map. Its target uses the actual scheme fibre
product and ordinary `Scheme.Modules.pullback` coefficient.
`_quasiIso` proves this literal arrow is a quasi-isomorphism.
`_inclusion` proves its exact chain square with the original model-to-Cech
map, original finite inclusions and original integer Cech base-change arrow.

`D.baseChangeCohomologyLinearEquiv e hflat σ q` identifies native homology
of the actual scalar-extended complex with unchanged cohomology of the
ordinary pulled coefficient, in every nonnegative degree and with its
original structural `B`-action. Its `_apply` formula retains the native
homology map of the same scalar-extended comparison.
The new ring need be neither flat nor Noetherian. This computes homology
of the tensor complex; it does not assert that every degreewise map
`B ⊗ Hⁱ → Hⁱ` is invertible, or infer cohomology finiteness over an arbitrary
noncoherent new ring.

## Original degreewise base-change map

Import `Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.BaseChange`.
`D.baseChangeCohomologyLinearEquiv_one_tmul` identifies the native homology
mate of the literal scalar-extended model with the original geometric
pullback on unchanged cohomology. The companion
`baseChangeCohomologyLinearEquiv_homologyBaseChangeMap_one_tmul` uses the
original `moduleCohomologyBaseChangeMap` itself on the right.

`D.baseChangeCohomologyLinearEquiv_homologyBaseChangeMap` is the full
`B`-linear commuting square. The original cohomology base-change map,
precomposed with the tensor of `D.cohomologyLinearEquiv`, equals the native
model homology mate followed by `D.baseChangeCohomologyLinearEquiv`.
The original cohomology carriers remain in universe `u+1`, and the model
carriers remain in `u`. The theorem holds for every ring map and every
degree, including zero. It requires actual relative flatness of the
coefficient but no flatness of the ring map; once `D` is given it has no
Noetherian hypothesis. The proof uses the actual comparison's homology
naturality and the original bounded Cech geometric normalization.

## Native derived objects after every base change

Import `Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.DerivedBaseChange`.
`D.baseChangePlus σ` is the native bounded-below packing of the literal
scalar-extended complex. `D.baseChangeToCechPlus σ e hflat` uses the actual
base-change comparison and the original finite inclusion on the fibre
product. Its `_hom_eq` formula retains the original tensor of
`D.toCechPlus.hom` followed by the original integer Cech base-change arrow;
`_quasiIso` proves that this same map is a quasi-isomorphism.

`D.baseChangeDerivedGlobalSectionsIso σ e hflat I` is an actual native
derived-object isomorphism from `QPlus` of that tensor complex to the
installed structural-ring derived global sections of ordinary `p* M` on
the actual fibre product. Here `I` is an actual module-sheaf injective
resolution of that ordinary coefficient. The `_hom` formula keeps the
localized literal chain map and the original module Cech/derived-unit
comparison; it is independent of the proof of affine tuple intersections.
The new ring need be neither flat nor Noetherian. No object isomorphism
is inferred merely from isomorphisms of homology modules.

## Actual original injective-resolution section model

Import `Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.Resolution`.
`D.resolutionSectionsDerivedIsoPlus e I` composes the original native
derived-global-sections model with the inverse original derived unit for
the actual module injective resolution `I`. Its ambient version
`resolutionSectionsDerivedIso` keeps both native inclusion factors.

`D.resolutionSectionsComparison e I` is an actual chain map from the same
projective complex to the actual structural-ring sections of that original
integer injective resolution. It is a quasi-isomorphism, and its
`_Q_map` theorem fixes its literal native localization to the original
derived comparison above. K-projectivity of the bounded projective source
constructs the representative; no projectivity of the resolution section
terms is assumed. Choice does not change the asserted derived map.
No Noetherian or relative-flat premise is needed once `D` is supplied.
The leaf passed with receipt `1792104658495672000-68178`.
The external `ProjectiveResolutionComparisonConsumer.lean` passed with
receipt `1792104721196905000-69378`, checking the actual arrow, its
quasi-isomorphism and its exact original `Q.map` normalization in arbitrary
universe `u`. The five inspected constructors and equations use only the
three standard axioms.

`BaseChangeResolution` supplies the same actual resolution-section map
after every ring map. `D.baseChangeResolutionSectionsComparison σ e hflat I`
is an actual quasi-isomorphism from the literal scalar-extended original
complex to sections of an actual injective resolution of ordinary `p* M`.
The `_Q_map` formula fixes its localization to the original proved
all-base-change derived comparison and inverse resolution unit. The new
ring need be neither Noetherian nor flat, and the target injective
resolution is chosen independently; no preservation of injectives under
pullback is asserted. The leaf passed with receipt
`1792105766891542000-88923` under the default budget.
The independent `ProjectiveBaseChangeResolutionConsumer.lean` passed with
receipt `1792105878730260000-90784`; its five inspected original arrows,
quasi-isomorphisms and exact localization equations use only the three
standard axioms.

## Actual sheaf-model comparison

Import `Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.Sheaf`.
`D.strictSheafModel` is the existing strict-perfect object given by native
tilde of the same finite-projective complex; `strictSheafModelPlus` packs
that literal same sheaf complex in the native bounded-below category.
`D.sheafComparison e I` is an actual map to the original pushed integer
injective resolution. It composes tilde of the normalized actual section
comparison, the inverse original spectrum section comparison, and the
original affine tilde/global-sections counit. Its `_f` formula retains the
original `fromTildeΓ` on each actual pushed term.

The `_of_counit` composition criteria retain explicitly the mathematical
condition that this original affine counit is a quasi-isomorphism.
Under that condition, the actual pushed resolution has native
`HasStrictModel`, and `derivedPushforwardIsoOfCounit` gives an actual
native derived-object isomorphism to the installed original `Rf_*` of the
coefficient in degree zero. Its `_hom` is the localized literal sheaf
arrow followed by the original injective-resolution derived unit.
The former `derivedPushforwardIso_of_counit` remains a transparent deprecated
alias, and the existing `derivedPushforwardIso_of_counit_hom` component formula
retains its name. These criteria alone do not discharge the geometric counit
condition and are
not a claimed perfect-direct-image existence theorem. The actual geometric
supplier must prove that condition. This assembly leaf passed with receipt
`1792105536129155000-85637` under the default budget.
The external `ProjectiveStrictSheafComparisonConsumer.lean` passed with
receipt `1792105600216526000-86861`; the seven inspected original-arrow,
strict-model and conditional native `Rf_*` comparison declarations use
only the three standard axioms.

The sole generic implementation now lives in
`Aglib.AlgebraicGeometry.Modules.Perfect.Affine.Model`. The projective
names delegate to its original `tildeModelMap`, retaining the same actual
section map and counit. The lower leaf passed with receipt
`1792106108684125000-94026`, and the projective delegation passed with
receipt `1792106203508648000-95466`. The refreshed independent sheaf
consumer passed with receipt `1792106419136475000-98324`, with only the
same three standard axioms.

## Perfect derived direct images

Import `Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.Perfect`.
`D.sheafComparison_quasiIso e I` proves the actual comparison to the
original pushed injective resolution is a quasi-isomorphism. The proved
qcqs affine counit theorem discharges the condition retained by the lower
composition criterion. `D.hasStrictSheafModel e I` gives the existing
native strict-model witness, and `D.derivedPushforwardIso e I` identifies
the same native strict perfect complex with the installed original
`rightDerivedFunctorPlus` of pushforward applied to the coefficient in
degree zero. Its `_hom` retains the literal localized sheaf comparison
and the original injective-resolution derived unit.

`exists_strictPerfect_derivedPushforward_of_projectiveEmbedding` constructs
this model directly from the given closed embedding, enumeration,
factorization, Noetherian base, coherent coefficient and relative base
flatness. Its actual sheaf terms lie in degrees `[0,n]`. There is no model
or counit-comparison input. The leaf passed with receipt
`1792106576037680000-441`; the independent
`ProjectivePerfectDirectImageConsumer.lean` passed with receipt
`1792106876856067000-4795`. Its actual arrows, strict-model witness, native
derived-object comparison and constructed existence theorem use only the
three standard axioms.

Import
`Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.BaseChangePerfect`
for every ring map `σ : R →+* B`. `D.baseChangeStrictSheafModel σ` is native
tilde of the literal scalar extension of the same original projective
complex. `baseChangeSheafComparison` maps it to the actual pushed
injective resolution of the ordinary pulled coefficient on the fibre
product. Its quasi-isomorphism is proved, and
`D.baseChangeDerivedPushforwardIso σ e hflat I` identifies this same
strict perfect complex with the installed derived pushforward on
`Spec B`. The `_hom` formula keeps the original chain map and derived unit.

`exists_strictPerfect_derivedPushforward_baseChange_of_projectiveEmbedding`
constructs that native model, with the same strict bounds `[0,n]`, from
the original geometric hypotheses and `σ`. Only the original ring must
be Noetherian; the new ring need be neither Noetherian nor flat over it.
The coefficient is ordinary pullback, and no finiteness of its cohomology
over a noncoherent new ring is inferred. The leaf passed with receipt
`1792107009378298000-6510`; the independent
`ProjectiveBaseChangePerfectDirectImageConsumer.lean` passed with receipt
`1792107141271240000-8810`. Its seven inspected constructors and equations
use only the three standard axioms.

## Remaining interfaces

Ordinary pulled coefficients are not identified with derived coefficient
pullback when the square is not Tor independent.

The native derived-global-sections model and its actual all-base-change
derived-object comparison are established here. A comparison to a globally
installed left-derived scalar-extension functor is separate: the pinned
Mathlib has no such bounded-above functor yet. Extension of the actual
perfect-direct-image supplier from projective embeddings to all proper
morphisms remains a separate required endpoint. The stronger arbitrary-base
proper finite-presentation tier is not discharged by this Noetherian supplier.

## Validation

The shared guarded wrapper compiled the actual supplier with receipt
`1792099073251975000-67786`, then the native derived comparison and exact
all-base-change chain square with receipt `1792099413023696000-74219`.
The final source, including source and all-base-change homology-map
normalizations, passed with receipt `1792099920579572000-82906` after the
coordinated lower-owner extraction. No whole-library build is used.

The independent external
`work/proper-validation/ProjectiveFiniteModelConsumer.lean` passed with
receipt `1792100202455424000-88101`. It checks the actual constructed
supplier, strict bounds, finite projective terms, literal scalar-extended
comparison, unchanged source and pulled-coefficient cohomology, exact
chain square, and native derived-global-sections object comparison.
Once model data is supplied, the comparison-interface checks have no
Noetherianity or flat-base-change premise. All eight inspected constructors
and canonical comparison declarations use only `propext`, `Classical.choice`,
and `Quot.sound`.

The canonical degreewise base-change leaf passed alone with receipt
`1792103228593669000-40293` under the default budget.
The independent `ProjectiveFiniteModelBaseChangeConsumer.lean` passed with
receipt `1792103292231192000-41131`, checking arbitrary universe `u` and every
degree with no Noetherian or flat-ring-map premise. The pure geometric unit,
original mate unit and full linear square use only the same three standard
axioms.

The native all-base-change derived-object leaf passed with receipt
`1792103582586318000-47872`; the independent all-universe
`ProjectiveDerivedBaseChangeConsumer.lean` passed with receipt
`1792103739213997000-51006`. Its actual chain-square identity,
quasi-isomorphism, derived-object comparison and forward formula use only
the same three standard axioms.

`Fibers` owns `D.fiberCohomologyDimension_eq_finrank`, the pointwise
comparison with the original ordinary residue-field fibre. Semicontinuity,
Euler characteristic and Grauert criteria share this sole declaration.
The original target structural action is retained explicitly.

`BaseChangeCriterion` transfers invertibility and epimorphy of the original
geometric map to the native homology mate of this same actual model.
`moduleCohomologyBaseChangeMap_isIso_iff` and
`moduleCohomologyBaseChangeMap_epi_iff` use the proved full linear square
and the actual source scalar-extension and target linear equivalences.
Original cohomology stays in universe `u+1`; the model stays in universe `u`.
No Noetherianity or flatness of the ring map is required once the model is
given. The public geometric Grauert consumer checks the native epimorphy
criterion independently, with only the standard three axioms.

## Shared model owner

The sole model record and construction now live in
[FiniteModel/Basic](../../FiniteModel/Basic.lean), with its
[family guide](../../FiniteModel/README.md). `ProjectiveCohomologyModel`
is the transparent coordinate-cover specialization, retaining the old
qualified `.mk` and field access and all existing public methods as thin
delegation. The old source passed `1792123795908750000-61238`; its enhanced
original public consumer passed `1792123861038373000-62261` with only the
three standard axioms, including the literal all-ring comparison and
original inclusion/derived-unit equations. Existing resolution, sheaf,
numerical and fibre source implementations remain unchanged in this move.

The canonical three base-change equations now delegate to the sole
[shared BaseChange owner](../../FiniteModel/BaseChange.lean), with the
same original geometric map, native homology mate, unit pure-tensor
formula and full mixed-universe linear square. The old wrapper passed
`1792124530024031000-70518`; the unchanged original public consumer passed
`1792124584660258000-71578` with only the standard three axioms. There is
no new flatness or Noetherianity premise on the target ring.

The original all-base-change derived-global-sections methods now delegate
to [shared Derived](../../FiniteModel/Derived.lean). Their exact names,
signatures, original scalar-extended integer Cech map and native derived
unit factors are retained. The old wrapper passed
`1792125107996662000-77649` in 3 seconds; the unchanged original
`ProjectiveDerivedBaseChangeConsumer.lean` passed
`1792125137568494000-78077` with only the standard three axioms for all
four inspected declarations. No resolution, sheaf or numerical consumer
source changed in this extraction.

The original `fiberCohomologyDimension_eq_finrank` now delegates to the
sole [shared Fibers owner](../../FiniteModel/Fibers.lean), retaining its
exact old statement, ordinary fibre and structural residue-field action.
The old wrapper passed `1792126437887773000-87565`; the unchanged original
Euler consumer passed `1792126574816467000-88998`, with only the three
standard axioms for its two inspected declarations. The same lower proof
also passed an internally constructed proper-model consumer in arbitrary
universe `u` (`1792126612714972000-90284`).

The two original `moduleCohomologyBaseChangeMap_isIso_iff` and `_epi_iff`
methods now thinly delegate to the sole
[shared BaseChangeCriterion owner](../../FiniteModel/BaseChangeCriterion.lean).
The old exact public statements and native maps are preserved. The old
wrapper passed `1792126747172015000-91610`; the unchanged original Grauert
consumer passed `1792126773999586000-91838`, and the same lower proof on an
internally constructed proper model passed `1792126810983862000-92117`.
All inspected declarations use only the standard three axioms.

The model-level upper-semicontinuity proof is now uniquely in
[shared Semicontinuity](../../FiniteModel/Semicontinuity.lean). The old
`Projective/Semicontinuity` interface and its geometric supplier retain
both exact public statements by thin specialization. The old leaf passed
`1792127403413653000-98249` and its unchanged original public consumer
`1792127442874241000-98742`, with only the standard three axioms.

Both original model-level Euler statements now thinly delegate to
[shared EulerCharacteristic](../../FiniteModel/EulerCharacteristic.lean).
The old names, intrinsic alternating sum, strict support argument and
original geometric endpoint remain unchanged. Source
`1792127605022548000-229` and unchanged original consumer
`1792127629970824000-658` passed, with only standard axioms.

The two reduced global model-level Grauert proofs now uniquely live in
[shared Grauert/Global](../../FiniteModel/Grauert/Global.lean). The old
`Projective/Grauert/Global` retains all four exact public statements and
its actual embedding-based suppliers as thin specializations. The old
source `1792127923492986000-3850` and unchanged original public consumer
`1792128019349233000-4538` passed, with only standard axioms. Reducedness
remains explicit, and no local-ring hypothesis is introduced globally.

The local model-level Grauert proof now uniquely lives in
[shared Grauert](../../FiniteModel/Grauert.lean). The old
`Projective/Grauert` retains both exact public statements and the original
embedding supplier as thin specialization, with both reducedness and the
local-ring guard. Old source `1792128390040003000-8348` and unchanged
original consumer `1792128437382519000-9057` passed, standard axioms only.
The six numerical owner moves preserve all fourteen old theorem
signatures exactly; original fibre and Euler definitions remain unchanged.
