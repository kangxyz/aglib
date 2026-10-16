# Finite projective complex models and criteria

This family works with Mathlib's actual `CochainComplex`, `HomologicalComplex.homology`,
`ModuleCat.extendScalars`, projective-object classes, and `Retract`. It introduces no
replacement derived category, perfect-complex object, or cohomology theory.

## Finite-free covers of original homology

[HomologyCover](HomologyCover.lean) proves
`HomologicalComplex.exists_finiteFree_single_homology_epi`. For any complex
shape and degree `i`, finite generation of the original `K.homology i`
gives an actual finite-free module `P` and actual chain map
`single_i P ⟶ K` whose original native homology map in degree `i` is an
epimorphism. The construction lifts a finite generating family through the
original cycle-to-homology epimorphism by native projectivity and retains
the native single-complex homology normalization.

Only the chosen homology module is assumed finite. No flatness, term
bound, Noetherianity or finiteness of other homology modules is needed.
The ring, module carrier and index universes are explicit; the carrier is
`max u v`, so the finite-free source lies in the original module category.
This is the first step toward an actual finite-projective replacement,
not a premise asserting the existence of that replacement.

The leaf passed with receipt `1792096816073803000-19397`. Its external
`work/proper-validation/FiniteFreeHomologyCoverConsumer.lean` passed with
receipt `1792096939997860000-22695`, checking an arbitrary complex shape
and a cochain specialization with carriers above the ring universe.
The construction uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Actual cone reduction of bounded flat complexes

[ConeStep](ConeStep.lean) proves
`CochainComplex.exists_finiteFree_single_top_reduction K n`. Suppose `R` is
Noetherian, `K` is strictly supported in `[0,n+1]`, every original term is
flat, and every original homology module is finite. The construction gives
an actual finite-free `P` and actual `single_(n+1) P ⟶ K`, epic on the
original top homology. For this very map, the original signed cone's good
truncation `L := (mappingCone φ).truncLE n` is strictly supported in `[0,n]`,
has flat terms and finite original homology, and its original inclusion into
the cone is a quasi-isomorphism.

Native cone homology exactness lowers the cohomological bound. Finite modules
form a Serre class over the Noetherian ring, giving actual cone-homology
finiteness; native homology of the original truncation inclusion transfers
it to `L`. Bounded-above flat cycle descent proves flatness of its actual
boundary. No family asserting base-change computations or a desired model
is assumed. Reassembly of these reductions into a finite-projective complex
is a separate subsequent construction.
The leaf passed with receipt `1792097986485327000-47023`.
The external `work/proper-validation/FiniteFreeConeReductionConsumer.lean`
passed with receipt `1792098104796643000-49100`, checking actual top-homology
surjectivity, original truncated terms and homology, and the literal native
inclusion. The construction uses only the same three standard axioms.

## Constructed finite-projective replacement

[Replacement](Replacement.lean) proves
`CochainComplex.exists_finiteProjective_model K n`. Over a Noetherian
commutative ring, assume the actual complex `K` is strictly supported in
`[0,n]`, has flat original terms and finite original homology in every
degree. The theorem constructs an actual complex `P` with the same strict
bounds, finite projective terms, and an actual quasi-isomorphism `P ⟶ K`.
It requires no supplied model or comparison family.

The induction uses the preceding actual top homology cover and shorter
flat truncation. Native twice-rotated cone reassembly supplies the chain
map back to `K`. Its native term isomorphism identifies each new term with
the biproduct of the actual shorter-model term and finite-free single term.
In degree-zero length, finite flat modules are finitely presented over the
Noetherian ring and hence projective by the native equational criterion.

`exists_finiteProjective_model_with_baseChange` proves that the same literal
map `u : P ⟶ K` remains a quasi-isomorphism under the original scalar-extension
functor for every ring homomorphism. This is derived from the proved
bounded-above acyclic flat cone theorem; it is not an extra premise on the
chosen model. Ring, module carrier and target-ring universes remain explicit,
and the new ring need be neither flat nor Noetherian. No finiteness of
homology over an arbitrary noncoherent new ring is inferred from this model.
The leaf passed with receipt `1792098641334337000-59671`.
The external `work/proper-validation/FiniteProjectiveReplacementConsumer.lean`
passed with receipt `1792098824946330000-63075`. It keeps the original ring
in `Type u`, module carriers in `Type (u+1)`, and arbitrary new rings in
`Type (u+2)`, retaining the literal mapped replacement map. Both inspected
replacement theorems use only the same three standard axioms.

## Projective models and arbitrary base change

[BaseChange](BaseChange.lean), imported as
`Aglib.Algebra.Homology.FiniteProjective.BaseChange`, supplies:

- the lower `ModuleCat.extendScalars_additive` instance, imported from
  `Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive`, including independent ring and
  module universes;
- `ModuleCat.finite_extendScalars` and `projective_extendScalars`, imported from their
  sole lower owner `Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness`, and
  their actual complex-term specializations `CochainComplex.finite_X_extendScalars`
  and `projective_X_extendScalars`;
- `CategoryTheory.Functor.quasiIso_mapHomologicalComplex_of_isKProjective` and
  `quasiIso_mapHomologicalComplex_of_projective`: any additive functor between abelian
  categories preserves the displayed quasi-isomorphism between K-projective complexes,
  or between projective complexes with explicit, possibly different strict upper bounds;
- `CochainComplex.quasiIso_extendScalars_of_projective`, applying the preceding statement
  to the native scalar-extension functor for an arbitrary homomorphism of commutative rings.

The proof maps the actual homotopy equivalence supplied by Mathlib's K-projectivity
criterion. The comparison map remains the original mapped chain map. Finiteness is not
needed for this independence of projective models. Mathlib already transports the same
strict lower and upper term bounds through zero-preserving functors. These results do
not say that arbitrary tensor product commutes with every individual homology module.

The primitive finite/projective module declarations retain the same names,
proofs and independent universes after extraction to the lower owner. That
leaf passed with receipt `1792093761512260000-66306`; the changed BaseChange
consumer then passed separately with receipt `1792093805076755000-66784`.

## Splitting an exact projective tail

[Cycles](Cycles.lean), imported as `Aglib.Algebra.Homology.FiniteProjective.Cycles`,
imports the actual short exact cycle sequence
`K.cycles n → K.X n → K.cycles (n + 1)` when `K` is exact in degree `n + 1`,
from its sole lower owner `CochainComplex.Cycles`. The generic short-exact
statement has no projective premise and retains its original name and proof.
The lower extraction passed with receipt `1792096965456898000-23506`;
this changed consumer then passed with receipt `1792097031365973000-25172`.
`cyclesRetractOfExactAt` uses projectivity of those next cycles to give an actual
retraction of the native inclusion `K.iCycles n`.

For an abelian category, `projective_cycles_of_exact_above` assumes a strict upper term
bound, projective terms, and exactness in every degree strictly greater than `n`. It
proves that `K.cycles n` is projective by descending induction. If the incoming
differential is zero, `projective_homology_of_exact_above_of_d_eq_zero` transports this
along the native `K.isoHomologyπ`. The specialization
`projective_homology_of_isStrictlyGE_of_exact_above` assumes a strict lower term bound
at `n`, which ensures that this incoming differential is zero.

For modules over an arbitrary ring, `finite_cycles_of_exact_above` and
`finite_homology_of_exact_above` need only finiteness of the term in the displayed
degree, the strict upper bound, projective terms, and the same exact positive tail.
They need neither a lower bound nor a Noetherian hypothesis. Homology is a quotient
of the finite cycle module; without the zero incoming differential it need not be
projective.

## Canonical homology base change

[HomologyBaseChange](HomologyBaseChange.lean), imported as
`Aglib.Algebra.Homology.FiniteProjective.HomologyBaseChange`, is a compatibility
import for the canonical lower owners
`Aglib.Algebra.Homology.ShortComplex.Adjunction` and
`Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Homology`. These constructions
have no finite-projective premise. The former constructs
`CategoryTheory.Adjunction.homologyUnit` from the original adjunction unit on a
short complex and the native identity-functor and right-adjoint homology comparisons.
`homologyComparison` is its actual adjunction mate. This generic construction needs
an additive adjunction between abelian categories whose right adjoint preserves
homology. The unit equation and naturality are proved for the displayed maps.
When the displayed homologies are preserved, the mate is exactly the inverse of
Mathlib's `ShortComplex.mapHomologyIso`.

`ModuleCat.homologyBaseChangeMap` specializes that construction to native scalar
extension. Its unit equation, unit-pure-tensor formula, and coefficient naturality
retain the actual adjunction. The ring universes are independent; the module-carrier
universe includes the target-ring universe, as required by the native adjunction.
`HomologicalComplex.extendScalarsHomologyMap` is the same map on the associated
short complex, for any complex shape and degree.

`homologyBaseChangeMap_isIso_of_g_eq_zero` and
`extendScalarsHomologyMap_isIso_of_d_eq_zero` prove arbitrary base change in a
rightmost degree with zero outgoing differential. This uses the actual left and
right homology preservation supplied by cokernel preservation and the zero map,
with no flatness. `homologyBaseChangeMap_eq_mapHomologyIso_inv` identifies the literal
map with the native inverse comparison whenever scalar extension preserves homology;
flatness can supply that functorial premise through Mathlib's exactness theorem.

## The two-term local fibre criterion

[LocalCriterion](LocalCriterion.lean), imported as
`Aglib.Algebra.Homology.FiniteProjective.LocalCriterion`, gives a concrete local
criterion on the actual residue-field homology. Let `R` be a commutative local
ring and let `K` be strictly supported in degrees `-1, 0`. Suppose `K.X (-1)` is
finite and `K.X 0` is finite flat. If the native scalar extension to the residue
field has zero native homology in degree `-1`, then
`free_homology_zero_of_residue_homology_neg_one_isZero` proves that the native
`K.homology 0` is free. `finite_homology_zero_of_isStrictlyLE` proves it finite.
No Noetherian premise or projectivity premise on the degree `-1` term is used.

`finrank_homology_zero_eq_residue_homology_zero` identifies the rank of that finite
free module with the dimension of the actual residue-field degree-zero homology.
The equality uses the canonical scalar-extension homology map. Independently,
`extendScalarsHomologyMap_isIso_of_isStrictlyLE` proves that literal comparison is
invertible in any strict uppermost degree after every ring map, including non-flat
maps. Its ring and carrier universes retain the bound required by the native
extension/restriction adjunction.

The short-complex theorem
`CategoryTheory.ShortComplex.moduleCat_free_homology_of_residue_injective` is a
more general presentation criterion: the first term is finite, the middle term
is finite flat, the outgoing arrow is zero, and the first arrow becomes injective
over the residue field. It proves that the actual homology is free by the native
cokernel comparison and Mathlib's local module criterion.
`HomologicalComplex.free_homology_of_residue_injective` uses exactly the actual
predecessor and successor of the displayed degree in an arbitrary complex shape.

This is the displayed two-term case of the bounded criterion below. Obtaining a
bounded finite-projective model from proper coherent cohomology, and passing from
geometric-fibre inputs to these residue-field calculations, remain separate steps.

## Native cancellation steps

[Cancellation](Cancellation.lean) cancels a displayed lowest degree. For `K` strictly
at least `a`, zero actual residue-field homology at `a` detects injectivity of the
residue-field differential. If its source is finite and its target finite flat,
the original differential is a split injection, `K` is exact at `a`, and the actual
`K.πTruncGE (a + 1)` is a quasi-isomorphism. The boundary opcycles are free.
`finite_X_truncGE` supplies finite terms of any lower truncation over any ring;
`free_X_truncGE_succ_of_residue_homology_isZero` preserves free terms under this
cancellation. This one step requires no upper bound.

[UpperCancellation](UpperCancellation.lean) cancels a displayed highest degree.
A strict upper bound `b`, finite `K.X b`, and zero actual residue-field homology at
`b` imply zero actual `K.homology b`. The proof uses the original canonical
rightmost homology base-change map and Nakayama. The actual inclusion
`K.ιTruncLE (b - 1)` is a quasi-isomorphism. For finite free terms, the split
projective cycle criterion proves that its boundary cycles and all truncated terms
are finite free. No lower bound or Noetherianity is needed in that step.

[ResidueConcentration](ResidueConcentration.lean) iterates these actual cancellation
steps. Its negative-degree theorem starts from a lower bound `-m`, an arbitrary
upper bound, and finite free terms; vanishing of all negative native residue-field
homology gives a homotopy-equivalent finite-free complex strictly at least zero.
Its positive-degree theorem removes the positive term range from a nonnegative
complex with a natural-number upper bound. Both proofs transport the residue
homology through actual mapped homotopy equivalences. The residue-field map need
not be flat.

## Bounded residue concentration and the single model

[SingleModel](SingleModel.lean), imported as
`Aglib.Algebra.Homology.FiniteProjective.SingleModel`, proves
`exists_homotopyEquiv_single_of_residue_homology`. Over a commutative local ring,
let `K` have arbitrary integer lower and upper strict term bounds and finite
projective terms. If the native complex after scalar extension to the residue
field has zero native homology in every degree other than zero, then there is an
actual module `P`, finite and free over the original ring, and an actual
`HomotopyEquiv K ((CochainComplex.singleFunctor _ 0).obj P)`.

The proof derives finite freeness of the original projective terms over the local
ring, iterates the native truncation cancellations, and uses Mathlib's native
single-complex isomorphism. The integer bounds are enlarged when necessary; they
do not need to straddle zero. No Noetherian assumption is used.

The direct corollaries `finite_homology_zero_of_residue_concentration`,
`free_homology_zero_of_residue_concentration`, and
`isZero_homology_of_residue_concentration` concern exactly the original native
homology objects. `finrank_homology_zero_eq_residue_of_concentration` gives the
rank as the dimension of actual residue-field degree-zero homology.

`extendScalarsHomologyMap_isIso_of_homotopyEquiv_single` identifies the needed
canonical comparison for any displayed homotopy equivalence to a single module;
it needs neither a local ring nor finiteness. It uses the coefficient naturality
of the original adjunction-unit map and the actual homology maps of the displayed
homotopy equivalence. Consequently
`extendScalarsHomologyMap_isIso_of_residue_concentration` proves that literal map
invertible in every integer degree after every ring map, without flatness. Rings
and module carriers retain their explicit native universe bounds, including target
rings above the original ring universe.

## Boundary toward proper cohomology

The consumer is the proper cohomology and base-change construction. The algebraic
finite-projective replacement is proved above. The
[projective finite model](../../../AlgebraicGeometry/Cohomology/Projective/FiniteModel.lean)
constructs the actual model for a closed projective embedding over a Noetherian base,
with coherent relatively flat coefficient, its actual native derived-global-sections
isomorphism, and computation of unchanged `Sheaf.H` after every ring base change.
The chain representative retains the original integer Cech base-change map.

Identifying the original degreewise cohomology base-change mate with the model's
native homology mate, proving perfectness of the actual sheaf-valued `Rf_*`, and
extending the projective geometric supplier to arbitrary proper morphisms remain
separate obligations. No stronger arbitrary-base proper-finiteness or locally-free
cohomology-base-change theorem-family input is discharged by the Noetherian supplier.

## Focused validation

The shared guarded wrapper compiled only the named leaves:

- `build Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive`, receipt
  `.lake/verification/cohomology/1792072798344505000-51895`;
- `build Aglib.Algebra.Homology.FiniteProjective.BaseChange`, receipt
  `.lake/verification/cohomology/1792072860173092000-56333` (after moving additivity
  to its lower owner);
- `build Aglib.Algebra.Homology.FiniteProjective.Cycles`, receipt
  `.lake/verification/cohomology/1792072310267790000-20886`;
- `build Aglib.Algebra.Homology.FiniteProjective.HomologyBaseChange`, receipt
  `.lake/verification/cohomology/1792073278278485000-77784`;
- `build Aglib.Algebra.Homology.FiniteProjective.LocalCriterion`, receipt
  `.lake/verification/cohomology/1792074197034479000-51323`;
- `build Aglib.Algebra.Homology.FiniteProjective.Cancellation`, receipt
  `.lake/verification/cohomology/1792074876412712000-80502`;
- `build Aglib.Algebra.Homology.FiniteProjective.UpperCancellation`, receipt
  `.lake/verification/cohomology/1792075013701937000-81844`;
- `build Aglib.Algebra.Homology.FiniteProjective.ResidueConcentration`, receipt
  `.lake/verification/cohomology/1792075390640939000-91885`;
- `build Aglib.Algebra.Homology.FiniteProjective.SingleModel`, receipt
  `.lake/verification/cohomology/1792076077357629000-3070`;
- `probe work/proper/BoundedConsumer.lean`, receipt
  `.lake/verification/cohomology/1792076243634355000-3757`: actual bounded-complex
  finite/free H0, vanishing outside degree zero, and the literal canonical map in
  every degree are consumed over a target ring in `Type (u+1)` for `R : Type u`.
  The single-model, arbitrary-base-change, and rank theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`;
- `probe work/proper/Consumer.lean`, receipt
  `.lake/verification/cohomology/1792074642761901000-73134`: the actual finite/free H0
  and canonical base-change conclusions are consumed with module carriers in `Type (u+1)`
  over rings in `Type u`. Explicit universe arguments resolve the native `max` carrier bound.
  The local criterion, rank equality, cycle splitting, and geometric pasting theorem use
  only `propext`, `Classical.choice`, and `Quot.sound`.

The historical probe files were moved out of the checkout to the external task
directory `work/proper-validation/`; their receipts and original validation commands
above remain the recorded evidence. No aggregate library build was run.

The geometric target is a finite-projective model for the derived direct image
`Rf_* M`, together with canonical base-change maps and Grauert/local-freeness criteria.
Projective direct-image and base-change endpoints are the current geometric priority.
Constant fibre dimensions on a nonreduced base do not supply local freeness by
themselves; any constancy-based Grauert statement must retain its reduced-base or
other sufficient hypotheses. The pointwise residue-concentration theorems above
instead retain their explicit bounded finite-projective complex premises.
