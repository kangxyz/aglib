/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Global

/-!
# The base of a flat family is the disjoint union of its flattening strata

Let `A` be a ring, `s : S ⟶ Spec A` with `S` locally Noetherian, `ι ≃ Fin (n + 1)`,
`X_S = P^n_A ×_{Spec A} S` and `F` a coherent module on `X_S` that is flat over `S`
(`relativeFlat (pullback.snd (toSpec A ι) s) F`). Then the fibre Hilbert polynomial
`y ↦ P_y = fiberHilbertPolynomialAt ι s F y` is locally constant
(`isLocallyConstant_fiberHilbertPolynomialAt_of_relativeFlat`) and `S` is the disjoint union of
the open and closed subschemes where it takes a given value. This is the decomposition used by
Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, p. 4 ("If F is flat
over S then the function s ↦ Φ_s ... is known to be locally constant on S. This shows that the
functor Quot naturally decomposes as a co-product"), and in the proof of Thm 4.3 (ii), p. 22
("Let T_f be the open and closed subscheme of T where the Hilbert polynomial is f"). Here it is a
corollary of Thm 4.3 over a locally Noetherian base (`FlatteningStratification/Global`): the
identity of `S` factors through the monomorphism `∐ S_f ⟶ S` (`mono_flatteningStrataι`,
`exists_lift_flatteningStrataι_of_relativeFlat`), so no separate local-constancy argument is
needed. Over an affine base the same local constancy is
`isLocallyConstant_projectiveHilbertPolynomial_fiber`
(`Cohomology/Projective/HilbertPolynomial/FlatFamily`); for a proper flat family the point-fibre
Euler characteristics are locally constant by
`isLocallyConstant_modulePointFiberEulerChar_of_proper` (`Cohomology/Proper/EulerCharacteristic`;
Stacks, Tag 0B9T), an independent route through a different interface.

* `isLocallyConstant_fiberHilbertPolynomialAt_of_relativeFlat`: `y ↦ P_y` is locally constant.
* `isIso_flatteningStrataι_of_relativeFlat`: `∐ S_f ⟶ S` is an isomorphism, `f` over the
  polynomials that occur (`exists_flatteningStrataι_section_of_relativeFlat`: the identity of `S`
  lifts).
* `isOpenImmersion_flatteningStratumι_of_relativeFlat`: every stratum `S_f ⟶ S` is an open
  immersion (with image `{y | P_y = f}`, `range_flatteningStratumι`; empty unless `f` occurs).
* `isOpen_setOf_fiberHilbertPolynomialAt_eq_of_relativeFlat`,
  `isClopen_setOf_fiberHilbertPolynomialAt_eq_of_relativeFlat`: `{y | P_y = f}` is open and
  closed.
* `exists_flatteningStratumι_apply_eq`: if the range of `φ : J → ℚ[X]` contains every `P_y`, the
  strata `S_{φ j}` cover `S` (no flatness needed).
* `isIso_sigmaDesc_flatteningStratumι_of_relativeFlat`: for any injective family
  `φ : J → ℚ[X]` whose range contains every `P_y` (for instance a finite set of polynomials `F`
  with `φ = Subtype.val`), `∐_j S_{φ j} ⟶ S` is an isomorphism; `flatteningDecompositionIso` is
  this isomorphism.
* **Maps out of `S`.** `flatteningStratumι_flatteningDecompositionIso_inv` and
  `hom_ext_of_flatteningStratumι_of_relativeFlat`: a morphism out of `S` is
  `(flatteningDecompositionIso …).inv` followed by `Sigma.desc` of its restrictions to the strata,
  and is determined by them.

For quasi-compact `S` only finitely many `f` occur (`finite_range_fiberHilbertPolynomialAt`,
`FlatteningStratification/AffineBase`). Present consumer: the clopen decomposition of a flat
family of closed subschemes by fibre Hilbert polynomial (`HilbertScheme/Coproduct/Decomposition`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}} [IsLocallyNoetherian S]
  (s : S ⟶ Spec (CommRingCat.of A)) (n : ℕ) (e : ι ≃ Fin (n + 1))
  {F : (pullback (toSpec A ι) s).Modules}
  (hF : affineLocallyFiniteType (pullback (toSpec A ι) s) F)
  (hflat : relativeFlat (pullback.snd (toSpec A ι) s) F)

include hflat in
/-- **For a flat `F`, the identity of `S` factors through the strata** (Nitsure,
arXiv:math/0504590v1, Thm 4.3 (ii), p. 19, for the test scheme `S` itself). -/
theorem exists_flatteningStrataι_section_of_relativeFlat :
    ∃ h : S ⟶ flatteningStrata ι s n e hF, h ≫ flatteningStrataι ι s n e hF = 𝟙 S := by
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  exact exists_lift_flatteningStrataι_of_relativeFlat ι s n e hF (𝟙 S)
    (relativeFlat_pullback_snd _ (𝟙 S) F hflat)

include hflat in
/-- **The base of a flat family is the disjoint union of its strata**: for `F` flat over `S`, the
monomorphism `∐ S_f ⟶ S` (`f` over the polynomials that occur) is an isomorphism, since the
identity of `S` factors through it. -/
theorem isIso_flatteningStrataι_of_relativeFlat : IsIso (flatteningStrataι ι s n e hF) := by
  have := mono_flatteningStrataι ι s n e hF
  obtain ⟨h, hh⟩ := exists_flatteningStrataι_section_of_relativeFlat ι s n e hF hflat
  exact ⟨⟨h, by rw [← cancel_mono (flatteningStrataι ι s n e hF), Category.assoc, hh,
    Category.comp_id, Category.id_comp], hh⟩⟩

include hflat in
/-- **The strata of a flat family are open immersions**: for `F` flat over `S`, every
`S_f ⟶ S` is an open immersion, onto `{y | P_y = f}` (`range_flatteningStratumι`). For `f` that
occurs it is a component of the isomorphism `∐ S_f ⟶ S`; otherwise `S_f` is empty. -/
theorem isOpenImmersion_flatteningStratumι_of_relativeFlat (f : Polynomial ℚ) :
    IsOpenImmersion (flatteningStratumι ι s n e hF f) := by
  by_cases hf : f ∈ Set.range (fiberHilbertPolynomialAt ι s F)
  · have := isIso_flatteningStrataι_of_relativeFlat ι s n e hF hflat
    have h := sigmaι_flatteningStrataι ι s n e hF ⟨f, hf⟩
    have : IsOpenImmersion (Sigma.ι (fun f : Set.range (fiberHilbertPolynomialAt ι s F) =>
        flatteningStratum ι s n e hF f) ⟨f, hf⟩ ≫ flatteningStrataι ι s n e hF) := inferInstance
    rw [h] at this
    exact this
  · have hempty : Set.range (flatteningStratumι ι s n e hF f) = ∅ := by
      rw [range_flatteningStratumι]
      exact Set.eq_empty_of_forall_notMem fun y hy => hf ⟨y, hy⟩
    have : IsEmpty (flatteningStratum ι s n e hF f) := Set.range_eq_empty_iff.mp hempty
    infer_instance

include e hF hflat in
/-- **The locus of a fibre Hilbert polynomial of a flat family is open**: for `F` flat over `S`,
`{y | P_y = f}` is the image of the open immersion `S_f ⟶ S`. -/
theorem isOpen_setOf_fiberHilbertPolynomialAt_eq_of_relativeFlat (f : Polynomial ℚ) :
    IsOpen {y | fiberHilbertPolynomialAt ι s F y = f} := by
  have := isOpenImmersion_flatteningStratumι_of_relativeFlat ι s n e hF hflat f
  rw [← range_flatteningStratumι ι s n e hF f]
  exact (flatteningStratumι ι s n e hF f).isOpenEmbedding.isOpen_range

include e hF hflat in
/-- **The fibre Hilbert polynomial of a flat family is locally constant** (Nitsure,
arXiv:math/0504590v1, §1, p. 4, "If F is flat over S then the function s ↦ Φ_s … is … locally
constant on S"): for `F` flat over the locally Noetherian base `S`, `y ↦ P_y` is locally
constant. -/
theorem isLocallyConstant_fiberHilbertPolynomialAt_of_relativeFlat :
    IsLocallyConstant (fiberHilbertPolynomialAt ι s F) :=
  IsLocallyConstant.iff_isOpen_fiber.mpr fun f =>
    isOpen_setOf_fiberHilbertPolynomialAt_eq_of_relativeFlat ι s n e hF hflat f

include e hF hflat in
/-- **Nitsure's `T_f`** (arXiv:math/0504590v1, proof of Thm 4.3 (ii), p. 22, "the open and closed
subscheme of T where the Hilbert polynomial is f"): for `F` flat over `S`, `{y | P_y = f}` is open
and closed. -/
theorem isClopen_setOf_fiberHilbertPolynomialAt_eq_of_relativeFlat (f : Polynomial ℚ) :
    IsClopen {y | fiberHilbertPolynomialAt ι s F y = f} :=
  (isLocallyConstant_fiberHilbertPolynomialAt_of_relativeFlat ι s n e hF hflat).isClopen_fiber f

section Decomposition

variable {J : Type*} [Small.{u} J] (φ : J → Polynomial ℚ) (hφ : Function.Injective φ)
  (hP : ∀ y, fiberHilbertPolynomialAt ι s F y ∈ Set.range φ)

omit [Small.{u} J] in
include e hF hP in
/-- **The strata over a set of polynomials cover `S`**: if the range of `φ` contains every fibre
Hilbert polynomial, every point of `S` lies in the image of some `S_{φ j}`. No flatness is
needed. -/
theorem exists_flatteningStratumι_apply_eq (y : S) :
    ∃ j z, flatteningStratumι ι s n e hF (φ j) z = y := by
  obtain ⟨j, hj⟩ := hP y
  have hy : y ∈ Set.range (flatteningStratumι ι s n e hF (φ j)) := by
    rw [range_flatteningStratumι]
    exact hj.symm
  obtain ⟨z, hz⟩ := hy
  exact ⟨j, z, hz⟩

include hflat hφ hP in
/-- **The decomposition of the base of a flat family over a set of polynomials**: for `F` flat over
`S` and an injective family `φ : J → ℚ[X]` whose range contains every fibre Hilbert polynomial
`P_y`, the strata `S_{φ j}` are open immersions with pairwise disjoint images covering `S`, so
`∐_j S_{φ j} ⟶ S` is an isomorphism. For `J` the polynomials that occur this is
`isIso_flatteningStrataι_of_relativeFlat`; `J` may also be a finite set of polynomials containing
them. -/
theorem isIso_sigmaDesc_flatteningStratumι_of_relativeFlat :
    IsIso (Sigma.desc fun j => flatteningStratumι ι s n e hF (φ j)) := by
  have := fun f => isOpenImmersion_flatteningStratumι_of_relativeFlat ι s n e hF hflat f
  have : IsOpenImmersion (Sigma.desc fun j => flatteningStratumι ι s n e hF (φ j)) :=
    isOpenImmersion_sigmaDesc _ _ fun j j' hjj' => by
      change Disjoint (Set.range (flatteningStratumι ι s n e hF (φ j)))
        (Set.range (flatteningStratumι ι s n e hF (φ j')))
      rw [range_flatteningStratumι, range_flatteningStratumι]
      exact Set.disjoint_left.mpr fun y h₁ h₂ => hjj' (hφ (h₁.symm.trans h₂))
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [eq_top_iff]
  rintro y -
  obtain ⟨j, z, hz⟩ := exists_flatteningStratumι_apply_eq ι s n e hF φ hP y
  refine ⟨Sigma.ι (fun j => flatteningStratum ι s n e hF (φ j)) j z, ?_⟩
  rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  exact hz

/-- **The decomposition isomorphism** `∐_j S_{φ j} ≅ S` of the base of a flat family, for an
injective family of polynomials `φ` containing every fibre Hilbert polynomial
(`isIso_sigmaDesc_flatteningStratumι_of_relativeFlat`). -/
def flatteningDecompositionIso :
    (∐ fun j => flatteningStratum ι s n e hF (φ j)) ≅ S :=
  haveI := isIso_sigmaDesc_flatteningStratumι_of_relativeFlat ι s n e hF hflat φ hφ hP
  asIso (Sigma.desc fun j => flatteningStratumι ι s n e hF (φ j))

@[reassoc (attr := simp)]
theorem sigmaι_flatteningDecompositionIso_hom (j : J) :
    Sigma.ι (fun j => flatteningStratum ι s n e hF (φ j)) j ≫
        (flatteningDecompositionIso ι s n e hF hflat φ hφ hP).hom =
      flatteningStratumι ι s n e hF (φ j) :=
  Sigma.ι_comp_desc _ _

/-- The inverse of the decomposition isomorphism restricts to the inclusion of each stratum. -/
@[reassoc (attr := simp)]
theorem flatteningStratumι_flatteningDecompositionIso_inv (j : J) :
    flatteningStratumι ι s n e hF (φ j) ≫
        (flatteningDecompositionIso ι s n e hF hflat φ hφ hP).inv =
      Sigma.ι (fun j => flatteningStratum ι s n e hF (φ j)) j := by
  rw [← sigmaι_flatteningDecompositionIso_hom ι s n e hF hflat φ hφ hP j, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

include hflat hφ hP in
/-- **Morphisms out of the base of a flat family are determined on the strata**: two morphisms
`S ⟶ Y` that agree after every `S_{φ j} ⟶ S` are equal. -/
theorem hom_ext_of_flatteningStratumι_of_relativeFlat {Y : Scheme.{u}} {a b : S ⟶ Y}
    (h : ∀ j, flatteningStratumι ι s n e hF (φ j) ≫ a = flatteningStratumι ι s n e hF (φ j) ≫ b) :
    a = b := by
  rw [← cancel_epi (flatteningDecompositionIso ι s n e hF hflat φ hφ hP).hom]
  exact Sigma.hom_ext _ _ fun j => by
    rw [sigmaι_flatteningDecompositionIso_hom_assoc, sigmaι_flatteningDecompositionIso_hom_assoc,
      h j]

end Decomposition

end AlgebraicGeometry.Scheme.Cohomology
