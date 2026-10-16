# Relative-simplex tuple complexes

Import `Aglib.Algebra.Homology.Simplex.Relative`, or a focused leaf below.
The family under `Simplex/Relative/` computes actual native homology
of alternating tuple complexes with prescribed required vertices. Its current
consumer is the monomial decomposition of projective-chart Cech cohomology.

For `S : Set ι`, degree `n` is the actual module of functions
`({a : Fin (n + 1) → ι // S ⊆ Set.range a} → R)`. A face missing a required
vertex contributes zero. `S = Set.univ` means precisely surjective tuples.
These are native `ModuleCat`, cosimplicial objects, alternating coface-map
complexes, homology objects, homotopies and connecting maps. There is no
replacement derived category or supplied cohomology-comparison family.

The ring `R : Type u` may be any ring, the vertices are in `Type v`, and the
module carrier universe is `max u v`. The explicit finite top calculation
uses vertices `Fin (n + 1)`, so its scalar equivalence retains an arbitrary
ring universe. No field, Noetherian, or nontrivial-ring premise is imposed.

- [Basic](Relative/Basic.lean) constructs the genuine cosimplicial module and
  native `RelativeSimplex.complex`. `extendByZero`, `positionMap`,
  `extendByZero_positionMap` and `d_apply` retain the literal zero-extension
  convention and the differential `∑ j, (-1)^j • x(a ∘ j.succAbove)`.
- [Contraction](Relative/Contraction.lean) gives the actual insertion operator
  `prepend`, its zero-extended and signed deletion formulas, and the native
  `contraction : Homotopy (𝟙 (complex R S)) 0` when `S` is nonempty and omits
  the chosen vertex. `acyclic_of_nonempty_of_not_mem` kills all actual homology
  in that case, including degree zero.
- [OptionSequence](Relative/OptionSequence.lean) constructs the actual short
  exact sequence `C(Option ι, univ) → C(Option ι, range some) → C(ι, univ)`.
  Its first map is extension by zero; its second evaluates on tuples of old
  `some` vertices. `optionDeltaIso R ι n`, for nonempty `ι`, is the literal
  native connecting isomorphism `H^n(C(ι, univ)) ≅ H^(n+1)(C(Option ι, univ))`.
- [Reindex](Relative/Reindex.lean) gives the actual tuple relabeling and
  cosimplicial/complex isomorphisms under a bijection of vertex sets.
  `complexReindexIso_hom_f_apply` retains the original inverse-relabeling formula.
  Its pure tuple relabeling helpers allow independent vertex universes.
- [FiniteReindex](Relative/FiniteReindex.lean) handles the geometric universe
  boundary: for `R, ι : Type u` and small `κ : Type`,
  `complexReindexSmallIso e` is the actual native full-support complex
  isomorphism induced by `e : ι ≃ κ`, in `ModuleCat.{u} R` throughout.
  `fullSupportTopLinearEquivOfEquivFin n e` and
  `fullSupport_isZero_homology_of_ne_of_equivFin n e q hq` transport the native
  finite-simplex calculation without lowering the scalar universe.
  Their actual cycles-quotient normalization is evaluation on the chosen
  enumeration `e.symm`. The same formula is retained when a weight's actual
  required support is proved equal to full support.
- [Singleton](Relative/Singleton.lean) proves positive exactness for an omitted
  vertex even when `S` is empty; it identifies singleton full-support degree-zero
  homology with the scalar module through the native cycles quotient and tuple
  evaluation, and proves singleton positive exactness.
- [Finite](Relative/Finite.lean) proves
  `fullSupportTopLinearEquiv R n : (complex R (univ : Set (Fin (n + 1)))).homology n ≃ₗ[R] R`
  and `fullSupport_isZero_homology_of_ne n q hq` in every other degree. Its
  recursive top equivalence uses the original singleton evaluation, tuple
  relabeling by `finSuccEquiv' 0`, and the original native connecting isomorphisms.
- [Evaluation](Relative/Evaluation.lean) proves the precise `+1` normalization
  of that connecting map at the tuple formed by prepending `none`.
  `optionMiddle_d_apply` shows that every other deletion omits a required old
  vertex. `optionDeltaIso_hom_evaluation` uses the native concrete `δ_apply`
  theorem, actual cycles, and the original cycles quotient; it retains the
  explicit cardinality premise `Fintype.card ι = n + 1`.
- [Trace](Relative/Trace.lean) defines `identityTuple n` and proves that the
  existing `fullSupportTopLinearEquiv R n` is exactly evaluation on that increasing
  tuple. `fullSupportTopLinearEquiv_homologyπ` is the formula on original cycles
  followed by their original quotient; `fullSupportTopLinearEquiv_apply` is the
  formula for every native top homology class using its unique cycle representative.
  These equations fix the sign and scalar normalization, including the singleton base.
- [Empty](Relative/Empty.lean) proves that actual zero-cycles for empty required
  support are constant. `emptySupportHomologyZeroLinearEquiv j` computes native
  H0 by original vertex evaluation, for any chosen vertex and arbitrary ring,
  with no finiteness premise. Its original cycles-quotient formula, constant
  augmentation normalization and independence of the chosen vertex are proved.
  Positive exactness is `exactAt_succ_of_not_mem` applied to empty support.
- [Support](Relative/Support.lean) transports the original empty/full-support
  scalar comparisons along an actual equality of required supports. Both
  original cycles-quotient formulas are preserved: vertex evaluation in H0
  and increasing-identity-tuple evaluation in the top degree. Actual monomial
  supports can therefore consume the same native homology comparisons.

The finite calculation applies to the full-tuple relative-simplex complex.
A geometric monomial weight decomposition must identify its literal tuple
coefficients, restrictions and deletion differential with this complex. The
general ordered-Cech/full-tuple comparison is a separate assertion.

[Weights](Relative/Weights/README.md) supplies the separate entry
`Aglib.Algebra.Homology.Simplex.Relative.Weights` for the original coordinate
Laurent tuple complex and its actual native coproduct decomposition into
relative-simplex weights, with coefficient and face-map normalization.

Each leaf was compiled separately through the shared serialized wrapper:

| Leaf | Receipt |
| --- | --- |
| Basic | `1792078164755908000-23623` |
| Contraction | `1792078437173027000-25810` |
| OptionSequence | `1792078640724406000-27622` |
| Reindex, including independent pure tuple universes | `1792086007177685000-22325` |
| FiniteReindex, including enumeration trace normalization | `1792086550915762000-26385` |
| Singleton | `1792078917638842000-29202` |
| Finite | `1792079122478141000-31226` |
| Evaluation | `1792079391560984000-33234` |
| Trace | `1792079558192131000-34954` |
| Empty | `1792083367791256000-80159` |
| Support equality normalization | `1792085542401593000-18105` |
| Family entry | `1792083464060386000-82463` |

The external task probe `work/proper-validation/RelativeSimplexConsumer.lean`
checks arbitrary-ring top cohomology, all other-degree vanishing, the increasing
tuple formulas on cycles and on homology, the proper-support contraction, the
literal deletion formula, independent ring/vertex universes, and the identity
of `optionDeltaIso.hom` with the native connecting map. The inspected top
equivalence, vanishing, trace, connecting normalization, and contraction use
only `propext`, `Classical.choice`, and `Quot.sound`.
The successful consumer receipt is `1792079706351785000-36291`.

The external task probe `work/proper-validation/RelativeEmptyConsumer.lean`
checks empty-support native H0, the original cycles-quotient evaluation,
the constant augmentation and independence of the chosen vertex, in independent
ring and vertex universes. Its successful receipt is `1792083873444030000-88122`;
the inspected comparisons use only the same three standard axioms.
