# Finite affine covers and bounded cohomology models

Import `Aglib.AlgebraicGeometry.Cohomology.Cech.Finite`, or a focused leaf below.
The constructions use native section complexes, the original Mayer–Vietoris
sequence, Mathlib's actual Cech complex, its zero extension and good truncation,
and the unchanged `Sheaf.H`. No new cohomology theory or comparison family is
introduced.

## Sharp bounds

[UnionBound](UnionBound.lean) gives
`Scheme.Cohomology.sectionsComplex_isLE_iSup_of_isAffineOpen`. Let `X` be separated,
let the abelian coefficient category admit the indicated sheafification, and let
`K` be an actual integer-indexed, termwise flasque sheaf complex. If its original
section complex is cohomologically at most zero on every affine open, then its
section complex on the union of `n + 1` affine opens is cohomologically at most
`n`. The proof applies the actual Mayer–Vietoris section sequence recursively.
The affine acyclicity premise here concerns the supplied arbitrary sheaf complex;
it is not an existence premise for a cohomology comparison.

[Vanishing](Vanishing.lean) supplies the concrete quasicoherent statement with
no affine-acyclicity premise:

- `subsingleton_sheafHPrime_sup` derives union vanishing from the actual native
  Mayer–Vietoris long exact sequence, using same-degree vanishing on the two
  opens and previous-degree vanishing on their intersection.
- `subsingleton_sheafHPrime_iSup_of_isAffineOpen` assumes separated `X`, an actual
  quasicoherent module sheaf `M`, and affine `U : Fin (n + 1) → X.Opens`. It proves
  native open-Ext `Sheaf.H'` vanishes on `iSup U` in every degree `q > n`.
- `subsingleton_sheafH_of_finite_affine_cover` adds the literal equality
  `iSup U = ⊤` and gives the same vanishing for the original `Sheaf.H`.

These results require no Noetherian, properness, finite-generation, or relative
flatness hypothesis. Separation supplies the affineness of intersections. The
actual affine quasicoherent acyclicity theorem discharges the local premise.

## A bounded structural-ring model

[Truncation](Truncation.lean) works over any explicit homomorphism
`α : R →+* Γ(X, ⊤)`, with the original module-valued Cech complex:

- `moduleCechIntFunctor` / `moduleCechIntComplex` extend the native Cech complex
  by zero from natural to integer degrees, functorially in the actual coefficient.
- `moduleFiniteCechFunctor` / `moduleFiniteCechComplex` apply native good upper
  truncation at `n`. The resulting complex is strictly supported in `[0, n]`.
- `moduleFiniteCechInclusion` is the original truncation inclusion.
  `moduleFiniteCechInclusion_naturality` proves its literal coefficient square.
- `moduleCechIntComplex_isLE` and `moduleFiniteCechInclusion_quasiIso` assume
  separated `X`, quasicoherent `M`, affine cover `U : ι → X.Opens`, its cover
  equality, and a specified enumeration `e : ι ≃ Fin (n + 1)`. They prove the
  sharp bound and that the original inclusion is a quasi-isomorphism.
- `moduleFiniteCechHomologyIso` uses the native homology map of that inclusion
  and the native zero-extension comparison.
- `moduleFiniteCechCohomologyLinearEquiv` identifies each nonnegative homology
  degree with the unchanged `Sheaf.H`, over the actual action induced by `α`.
  Degree zero uses the original section augmentation and the existing normalized
  `moduleCechCohomologyLinearEquivZero`; positive degrees use the original
  scalar-linear affine-Cech comparison with an actual additive injective resolution.

The scheme, structural ring, and cover index are in universe `u`; native Cech
modules have carrier universe `u`, and original Ext cohomology is in `u + 1`.
The finite enumeration avoids silently restricting the cover-index universe.

`moduleFiniteCechXIso` identifies every nonnegative term strictly below the
upper boundary with the original Cech section product. At the boundary,
`moduleFiniteCechTopIsoCycles` identifies the term with the actual cycles of
the untruncated integer Cech complex. Truncation alone claims neither
flatness nor finite generation of those boundary cycles. A finite cover
alone supplies neither finite generation of its section modules nor a
finite-projective model. [FlatModel](FlatModel.lean) below proves the boundary
flatness from the actual relative-flat coefficient and the proved universal
tensor exactness. An unbounded exact tail of flat terms does not suffice.

## Flat original section terms

[FlatTerms](FlatTerms.lean) fixes an actual structure morphism
`f : X ⟶ Spec R` and its literal structural map to global functions.
`moduleSectionsPresheaf_flat_of_relativeFlat` proves flatness of the existing
structural-ring section presheaf on affine opens, using the actual
quasicoherent coefficient and its relative flatness over the base stalks.
The original one-step section action and native two-step presheaf action are
compared by the original restriction-of-scalars composition isomorphism.

`moduleCechComplex_flat_X_of_relativeFlat` adds separated `X` and a finite
affine family. Every actual full-tuple Cech term is flat: its original native
product consists of the same affine-intersection section modules. The proof
uses the actual finite product/direct-sum comparison, without asserting that
an infinite product of flat modules is flat.
`moduleCechIntComplex_flat_X_of_relativeFlat` transports this to the unchanged
integer extension; negative terms are the original zero objects.
No cover equality, Noetherianity, properness, section finiteness, or flatness
of the scheme morphism is assumed for these term statements. A finite cover
alone still does not give finite-projective terms or section finiteness.

## Universal tensor exactness

[IntBaseChange](IntBaseChange.lean) extends the original natural-number Cech
base-change map through the native zero-extension comparison.
`moduleCechIntBaseChangeMap_f_extendXIso` retains its exact original component
in every nonnegative degree, using the native term transports on both sides.

[GeometricUnit](GeometricUnit.lean) retains the original scalar-forgetting
comparison and geometric pullback unit on this same integer complex.
`moduleCechIntTensorMapAlong_forget_unit` works with an actual coefficient
arrow and compatible structural ring maps; its specialization
`moduleCechIntBaseChangeMap_forget_unit` uses the literal ordinary-pullback
adjunction unit on the actual fibre product. These are chain identities for
every ring map. Apart from the finite cover-index type needed by the original
tensor Cech arrow, they require no cover equality, quasicoherence, affine
opens, flatness or homology preservation. The leaf passed alone with receipt
`1792102241171394000-23505`.
The external `CechIntGeometricUnitConsumer.lean` passed with receipt
`1792102272851899000-23791`; the comparison and both unit squares use only
`propext`, `Classical.choice` and `Quot.sound`.

[GeometricHomology](GeometricHomology.lean) identifies the original integer
scalar-forgetting homology comparison with the native `extendHomologyIso`
followed by the original natural-number Cech comparison.
`moduleCechIntBaseChangeHomologyMap_one_tmul` proves that the literal native
homology mate followed by the original integer Cech base-change arrow has
the original additive geometric unit formula. It retains the same minimal
hypotheses as the chain square above, with no exactness assumption on scalar
extension. The leaf passed with receipt `1792102705819869000-31041`.
Its external normalization consumer passed with receipt
`1792102794000901000-32470`, using only the three standard axioms.

[Geometric](Geometric.lean) proves
`moduleFiniteCechBaseChangeCohomologyLinearEquiv_one_tmul` in every degree,
including degree zero. For the actual relative-flat quasicoherent coefficient
and finite affine cover, the native homology mate of the original bounded
complex computes the unchanged geometric pullback on `Sheaf.H`. The proof
retains the original finite inclusion square and the native homology-mate
naturality; degree zero uses the original augmentation and positive degrees
use the original geometric Cech comparison. There is no flatness assumption
on the ring map, no Noetherianity and no cohomology-finiteness premise. The
leaf passed alone with receipt `1792102876932834000-34034`.
The external `FiniteCechGeometricConsumer.lean` passed with receipt
`1792102946388845000-35346`; the actual normalization uses only the three
standard axioms.
For a finite affine family in separated `X` and quasicoherent `M`, its
`moduleCechIntBaseChangeIso` is invertible for every ring map. No cover,
coefficient relative flatness or flatness of the ring map is required here.

[UniversalTensor](UniversalTensor.lean) adds the actual cover equality and
enumeration by `Fin (n+1)`. `moduleCechIntComplex_extendScalars_isLE` proves
the original extended complex obeys the same sharp bound after every ring
base change, including to non-Noetherian rings. The actual pulled coefficient
is quasicoherent, and the pulled affine opens form the original cover after
base change.

`moduleCechIntComplex_universally_lTensor_exact` then proves that the original
differentials in degrees `n`, `n+1`, `n+2` are exact after tensoring with
every base module. The lower native square-zero-extension test discharges
this universal module statement from the proved actual all-ring statement.
Neither relative flatness nor Noetherianity is assumed for this theorem.
Relative flatness is needed separately for the original section terms,
before applying the lower native flat-cycle/good-truncation criterion.

## The bounded flat model after every base change

[FlatModel](FlatModel.lean) combines these actual geometric suppliers. Its
hypotheses are a separated scheme `X`, structure morphism `f : X ⟶ Spec R`,
quasicoherent coefficient `M` relatively flat for this morphism, and an affine
cover with its equality and enumeration `e : ι ≃ Fin (n+1)`. The ring is an
arbitrary commutative ring. No Noetherianity, properness, finite generation
of sections, flatness of `f`, or flatness of a subsequent base change is assumed.

- `moduleCechIntComplex_flat_cycles_of_relativeFlat` proves that the actual
  cycles at the sharp cutoff `n` are flat. Universal next-degree tensor
  exactness is proved by the preceding geometric theorem, rather than supplied
  as an additional family of comparison assumptions.
- `moduleFiniteCechComplex_flat_X_of_relativeFlat` proves every term of the
  unchanged native good truncation is flat. The same complex has its original
  strict bounds `[0,n]`, original inclusion, and original cohomology comparison.
- `moduleFiniteCechBaseChangeIso` identifies the actual scalar extension of
  this bounded model with the bounded model on the actual scheme pullback,
  for every homomorphism `R →+* B`. The coefficient on that scheme is the
  ordinary module-sheaf pullback. Its `_hom_ιTruncLE` theorem retains the
  literal original mapped inclusion and integer Cech base-change arrow.
- `moduleFiniteCechInclusion_extendScalars_quasiIso` proves the original
  mapped truncation inclusion is a quasi-isomorphism for every such ring map.
- `moduleFiniteCechBaseChangeCohomologyLinearEquiv` computes the unchanged
  `Sheaf.H` of the ordinary pulled coefficient, in every nonnegative degree
  with its original structural `B`-module action, by the scalar-extended
  bounded flat source model.

This supplies a bounded flat model and its actual all-ring comparison. It
does not assert finite-projective terms, nor identify ordinary coefficient
pullback with derived coefficient pullback. The comparison with a native
derived direct-image object is a separate required interface.

## Validation

Each changed leaf was compiled separately through the shared serialized
`aglib-build-one.py` wrapper, without a whole-library build:

- `UnionBound`: receipt `1792077134163927000-12667`.
- `Vanishing`: receipt `1792077358960817000-14952`.
- `Truncation`: receipt `1792077654377371000-18238`.
- `FlatTerms`: receipt `1792093658686500000-64902`.
- `IntBaseChange`: receipt `1792094724099375000-83947`.
- `UniversalTensor`: receipt `1792095191419022000-90966`.
- `FlatModel`: receipt `1792096095873079000-4330`.
- Family entry leaf: receipt `1792077782611295000-19428`.

The external consumer `work/proper-validation/FiniteCechConsumer.lean` checks
both strict bounds, the literal inclusion quasi-isomorphism, every nonnegative
scalar-linear cohomology comparison, and coefficient inclusion naturality.
Its successful wrapper receipt is `1792077923344706000-21444`.
The inspected vanishing, inclusion, and linear-comparison declarations depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

The separate external `work/proper-validation/FiniteCechFlatTermsConsumer.lean`
checks the original structural section modules and every natural/integer Cech
term, with the exact relative-flat input and without a cover or Noetherian
hypothesis. It passed with receipt `1792093903199409000-68136`; the inspected
term-flatness proofs use the same three standard axioms.

`work/proper-validation/FiniteCechUniversalTensorConsumer.lean` checks the
original all-ring bound and literal all-module tensor differential pair,
without relative-flat or Noetherian assumptions or an extra finite-index
premise beyond the enumeration. Its receipt is `1792095488383892000-95585`.
The original integer component, base-change invertibility, all-ring bound
and universal module exactness use only the same three standard axioms.

`work/proper-validation/FiniteCechFlatModelConsumer.lean` checks the actual
boundary cycles, every bounded-model term, both strict bounds, original and
mapped inclusion quasi-isomorphisms, the literal base-change inclusion square,
and all-degree computation of the original cohomology after every ring map.
It passed with receipt `1792096438206314000-10371`; all five inspected flat-model
and canonical comparison declarations use only the same three standard axioms.

The finite-projective local fibre criterion is an independent lower family.
A finite-projective replacement still requires an actual algebraic construction
from the bounded flat model and appropriate cohomology finiteness. The stronger
arbitrary-base `LocalFreeCohomologyBaseChange` family remains explicit.
