/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The actual polynomial source of a local parameter family

The source is the localization at the kernel of the original residue point.
Its dimension is the coefficient-kernel height plus the number of variables.
No Jacobson hypothesis or replacement residue-field model is used.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsLocalRing

universe u

/-- An actual regular local parameter source, before completion. -/
structure PolynomialParameterSource (A : Type u) [CommRing A] [IsLocalRing A] (d : ℕ) where
  /-- The chosen regular local source ring. -/
  ring : CommRingCat.{u}
  regular : IsRegularLocalRing ring
  dimension : ringKrullDim ring = (d : ℕ)
  /-- The parameter map from the source ring to the original local ring. -/
  map : ring →+* A
  radical :
    let _ : IsRegularLocalRing ring := regular
    ((maximalIdeal ring).map map).radical = maximalIdeal A
  residue_surjective : Function.Surjective ((residue A).comp map)

namespace PolynomialParameterSource

theorem point_surjective {D K : Type*} [CommRing D] [Field K]
    (g : D →+* K) (hg : Function.Surjective g) (ι : Type*) :
    Function.Surjective (g.comp (MvPolynomial.constantCoeff : MvPolynomial ι D →+* D)) := by
  intro a
  obtain ⟨d, rfl⟩ := hg a
  exact ⟨MvPolynomial.C d, by simp⟩

/-- The height of the literal zero-variable residue point, over an arbitrary
Noetherian coefficient ring, without a Jacobson assumption. -/
theorem residuePoint_height {D K : Type*} [CommRing D] [IsNoetherianRing D] [Field K]
    (g : D →+* K) (hg : Function.Surjective g) (ι : Type*) [Finite ι] :
    (RingHom.ker (g.comp (MvPolynomial.constantCoeff : MvPolynomial ι D →+* D))).height =
      (RingHom.ker g).height + Nat.card ι := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    let E := (MvPolynomial.renameEquiv D e).toRingEquiv
    have he :
        (RingHom.ker (g.comp MvPolynomial.constantCoeff)).comap E =
          RingHom.ker (g.comp MvPolynomial.constantCoeff) := by
      ext F
      change g (MvPolynomial.constantCoeff (E F)) = 0 ↔
        g (MvPolynomial.constantCoeff F) = 0
      simp [E, MvPolynomial.renameEquiv_apply, MvPolynomial.constantCoeff_rename]
    rw [← E.height_comap, he, H, Nat.card_congr e]
  | h_empty =>
    let E := MvPolynomial.isEmptyRingEquiv D PEmpty
    have he : (RingHom.ker g).comap E =
        RingHom.ker (g.comp (MvPolynomial.constantCoeff : MvPolynomial PEmpty D →+* D)) := by
      rfl
    rw [← he, E.height_comap]
    simp
  | @h_option ι _ H =>
    let h : MvPolynomial ι D →+* K := g.comp MvPolynomial.constantCoeff
    let z : Polynomial (MvPolynomial ι D) →+* K := h.comp Polynomial.constantCoeff
    let q := RingHom.ker z
    let E := (MvPolynomial.optionEquivLeft D ι).toRingEquiv
    have hz : Function.Surjective z := by
      intro a
      obtain ⟨F, hF⟩ := point_surjective g hg ι a
      exact ⟨Polynomial.C F, by simpa [z, h] using hF⟩
    let : q.IsMaximal := RingHom.ker_isMaximal_of_surjective z hz
    have he : z.comp E.toRingHom = g.comp MvPolynomial.constantCoeff := by
      apply MvPolynomial.ringHom_ext
      · intro d
        simp [z, h, E]
      · intro i
        cases i <;> simp [z, h, E]
    have hq : q.comap E = RingHom.ker (g.comp MvPolynomial.constantCoeff) := by
      change (RingHom.ker z).comap E.toRingHom = _
      rw [RingHom.comap_ker, he]
    have hp : q.comap Polynomial.C = RingHom.ker h := by
      ext F
      simp [q, z, RingHom.mem_ker]
    let : q.LiesOver (RingHom.ker h) := ⟨hp.symm⟩
    rw [← hq, E.height_comap, Polynomial.height_eq_height_add_one (RingHom.ker h) q]
    change (RingHom.ker (g.comp MvPolynomial.constantCoeff)).height + 1 = _
    rw [H]
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      add_assoc]

theorem point_kernel {D K : Type*} [CommRing D] [CommRing K]
    (g : D →+* K) (ι : Type*) :
    RingHom.ker (g.comp (MvPolynomial.constantCoeff : MvPolynomial ι D →+* D)) =
      (RingHom.ker g).map MvPolynomial.C ⊔ Ideal.span (Set.range MvPolynomial.X) := by
  let J : Ideal (MvPolynomial ι D) :=
    (RingHom.ker g).map MvPolynomial.C ⊔ Ideal.span (Set.range MvPolynomial.X)
  have hfactor : Ideal.Quotient.mk J =
      ((Ideal.Quotient.mk J).comp MvPolynomial.C).comp MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro d
      simp
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.constantCoeff_X, map_zero]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))
  apply le_antisymm
  · intro F hF
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [DFunLike.congr_fun hfactor F]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem MvPolynomial.C hF)
  · apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro d hd
      simpa only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply,
        MvPolynomial.constantCoeff_C] using hd
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]

/-- The original evaluation map, localized at its literal residue-point kernel,
gives a regular local source of dimension `r + d` for the supplied parameters. -/
def ofParameters
    {D A : Type u} [CommRing D] [IsRegularRing D] [CommRing A] [IsLocalRing A]
    (f : D →+* A) (hres : Function.Surjective ((residue A).comp f))
    (r d : ℕ) (hheight : (RingHom.ker ((residue A).comp f)).height = (r : ℕ∞))
    (x : Fin d → A) (hx : ∀ i, x i ∈ maximalIdeal A)
    (hparam : ((RingHom.ker ((residue A).comp f)).map f ⊔
      Ideal.span (Set.range x)).radical = maximalIdeal A) :
    PolynomialParameterSource A (r + d) := by
  let g : D →+* ResidueField A := (residue A).comp f
  let e : MvPolynomial (Fin d) D →+* A := MvPolynomial.eval₂Hom f x
  let z : MvPolynomial (Fin d) D →+* ResidueField A := g.comp MvPolynomial.constantCoeff
  let q := RingHom.ker z
  let : q.IsMaximal := RingHom.ker_isMaximal_of_surjective z (point_surjective g hres _)
  let B := Localization.AtPrime q
  let : IsRegularLocalRing B := inferInstance
  have hpoint : (residue A).comp e = z := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e, z, g]
    · intro i
      simpa [e, z] using (residue_eq_zero_iff (x i)).mpr (hx i)
  have hunit (s : q.primeCompl) : IsUnit (e s) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    intro hs
    apply s.property
    change z s = 0
    rw [← hpoint]
    exact hs
  let fB : B →+* A := IsLocalization.lift (M := q.primeCompl) (S := B) (g := e) hunit
  have hlift (F : MvPolynomial (Fin d) D) : fB (algebraMap _ B F) = e F :=
    IsLocalization.lift_eq hunit F
  have hcomp : fB.comp (algebraMap (MvPolynomial (Fin d) D) B) = e :=
    RingHom.ext hlift
  have hq : q = (RingHom.ker g).map MvPolynomial.C ⊔
      Ideal.span (Set.range MvPolynomial.X) := point_kernel g _
  have hm : (maximalIdeal B).map fB =
      (RingHom.ker g).map f ⊔ Ideal.span (Set.range x) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hcomp, hq,
      Ideal.map_sup, Ideal.map_map, Ideal.map_span]
    have heC : e.comp MvPolynomial.C = f := by ext c; simp [e]
    rw [heC]
    have himage : e '' Set.range MvPolynomial.X = Set.range x := by
      ext a
      simp [e, Set.mem_image, Set.mem_range]
    rw [himage]
  have hdim : ringKrullDim B = ((r + d : ℕ) : ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q B]
    change ((RingHom.ker (g.comp MvPolynomial.constantCoeff)).height : WithBot ℕ∞) = _
    rw [residuePoint_height g hres, hheight]
    simp
  have hresB : Function.Surjective ((residue A).comp fB) := by
    intro a
    obtain ⟨c, hc⟩ := hres a
    refine ⟨algebraMap (MvPolynomial (Fin d) D) B (MvPolynomial.C c), ?_⟩
    change residue A (fB (algebraMap _ B (MvPolynomial.C c))) = a
    rw [hlift]
    simpa [e] using hc
  exact {
    ring := CommRingCat.of B
    regular := inferInstance
    dimension := hdim
    map := fB
    radical := by
      change ((maximalIdeal B).map fB).radical = maximalIdeal A
      rw [hm]
      exact hparam
    residue_surjective := hresB }

end PolynomialParameterSource
end IsLocalRing
