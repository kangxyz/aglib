/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Finite
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Evaluation of the actual vertex-removal connecting map

In the top degree, evaluating the original connecting homomorphism on the
tuple obtained by prepending `none` retains exactly the first deletion face.
Its coefficient is `+1`. This normalizes the native full-support top class
without an arbitrary scalar or sign choice.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace AlgebraicTopology.RelativeSimplex

variable {ι : Type v} {R : Type u} [Ring R] {n : ℕ}

/-- Prepending the new vertex to a full-support tuple gives a full-support tuple
on the enlarged vertex set. -/
def optionTuple (a : Tuple (Set.univ : Set ι) n) :
    Tuple (Set.univ : Set (Option ι)) (n + 1) :=
  ⟨Fin.cons none (Option.some ∘ a.val), by
    rintro (_ | i) hi
    · exact ⟨0, rfl⟩
    · obtain ⟨k, hk⟩ := a.property (Set.mem_univ i)
      exact ⟨k.succ, congrArg Option.some hk⟩⟩

/-- The same tuple viewed in the middle term of the vertex-removal sequence. -/
def optionMiddleTuple (a : Tuple (Set.univ : Set ι) n) :
    Tuple (Set.range (@Option.some ι)) (n + 1) :=
  ⟨(optionTuple a).val, fun i _hi => (optionTuple a).property (Set.mem_univ i)⟩

/-- At the top tuple every deletion except the first omits a required old vertex. -/
theorem optionMiddle_d_apply [Fintype ι] (hcard : Fintype.card ι = n + 1)
    (x : Cochains R (Set.range (@Option.some ι)) n) (a : Tuple (Set.univ : Set ι) n) :
    (complex R (Set.range (@Option.some ι))).d n (n + 1) x (optionMiddleTuple a) =
      x (someTuple a) := by
  rw [d_apply, Fin.sum_univ_succ]
  have hzero : (optionMiddleTuple a).val ∘ (0 : Fin (n + 2)).succAbove =
      (someTuple a).val := by
    funext k
    simp [optionMiddleTuple, optionTuple, someTuple]
  rw [hzero, extendByZero_apply]
  have hvan (k : Fin (n + 1)) :
      extendByZero x ((optionMiddleTuple a).val ∘ k.succ.succAbove) = 0 := by
    apply extendByZero_of_not_supported
    intro h
    have hnone : ((optionMiddleTuple a).val ∘ k.succ.succAbove) 0 = none := by
      change (Fin.cons none (Option.some ∘ a.val) ∘ k.succ.succAbove) 0 = none
      rw [Fin.cons_comp_succ_succAbove]
      rfl
    have hfull : Set.univ ⊆ Set.range ((optionMiddleTuple a).val ∘ k.succ.succAbove) := by
      rintro (_ | i) hi
      · exact ⟨0, hnone⟩
      · exact h ⟨i, rfl⟩
    have hc := Fintype.card_le_of_surjective _
      ((univ_supported_iff_surjective _).mp hfull)
    simp only [Fintype.card_fin, Fintype.card_option, hcard] at hc
    omega
  simp only [hvan, smul_zero, Finset.sum_const_zero, add_zero, Fin.val_zero,
    pow_zero, one_smul]

/-- In the lowest nonzero full-support degree there are no incoming boundaries,
so the actual cycles quotient is an isomorphism. -/
def fullSupportCyclesIso [Fintype ι] (n : ℕ) (hcard : Fintype.card ι = n + 1) :
    (complex R (Set.univ : Set ι)).cycles n ≅ (complex R (Set.univ : Set ι)).homology n := by
  cases n with
  | zero => exact (complex R (Set.univ : Set ι)).isoHomologyπ₀
  | succ n =>
    exact (complex R (Set.univ : Set ι)).isoHomologyπ n (n + 1) (by simp)
      ((isZero_X_of_card_lt n (by omega)).eq_of_src _ _)

@[simp]
theorem fullSupportCyclesIso_hom [Fintype ι] (n : ℕ) (hcard : Fintype.card ι = n + 1) :
    (fullSupportCyclesIso (R := R) n hcard).hom =
      (complex R (Set.univ : Set ι)).homologyπ n := by
  cases n <;> rfl

/-- The native connecting isomorphism has coefficient `+1` on the tuple formed
by prepending the new vertex. The cycles and their quotient are the original
ones, and the comparison is the original long-exact-sequence connecting map. -/
theorem optionDeltaIso_hom_evaluation [Fintype ι] [Nonempty ι]
    (hcard : Fintype.card ι = n + 1)
    (c : (complex R (Set.univ : Set ι)).cycles n) (a : Tuple (Set.univ : Set ι) n) :
    (complex R (Set.univ : Set (Option ι))).iCycles (n + 1)
      ((fullSupportCyclesIso (R := R) (n + 1) (by simp [hcard])).inv
        ((optionDeltaIso R ι n).hom ((complex R (Set.univ : Set ι)).homologyπ n c)))
        (optionTuple a) = (complex R (Set.univ : Set ι)).iCycles n c a := by
  let S := optionSequence R ι
  let hS := optionSequence_shortExact R ι
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  let x₃ : S.X₃.X n := S.X₃.iCycles n c
  have hx₃ : S.X₃.d n (n + 1) x₃ = 0 := by
    have h := ConcreteCategory.congr_hom (S.X₃.iCycles_d n (n + 1)) c
    exact h
  obtain ⟨x₂, hx₂⟩ :=
    (hS.map (HomologicalComplex.eval (ModuleCat.{max u v} R) (.up ℕ) n)).moduleCat_surjective_g x₃
  change S.g.f n x₂ = x₃ at hx₂
  have hz : S.g.f (n + 1) (S.X₂.d n (n + 1) x₂) = 0 := by
    have h := (ConcreteCategory.congr_hom (S.g.comm n (n + 1)) x₂).symm
    change S.g.f (n + 1) (S.X₂.d n (n + 1) x₂) = S.X₃.d n (n + 1) (S.g.f n x₂) at h
    rw [h, hx₂, hx₃]
  obtain ⟨x₁, hx₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (hS.map (HomologicalComplex.eval (ModuleCat.{max u v} R) (.up ℕ) (n + 1))).exact _ hz
  let z := S.X₁.cyclesMk x₁ (n + 2) (by simp)
    (hS.d_eq_zero_of_f_eq_d_apply n (n + 1) x₂ x₁ hx₁ (n + 2))
  have hc : S.X₃.cyclesMk x₃ (n + 1) (by simp) hx₃ = c := by
    apply (ModuleCat.mono_iff_injective (S.X₃.iCycles n)).mp inferInstance
    exact S.X₃.i_cyclesMk _ _ _ _
  have hδ : (hS.δ n (n + 1) (by simp)) (S.X₃.homologyπ n c) =
      S.X₁.homologyπ (n + 1) z := by
    have h := hS.δ_apply n (n + 1) (by simp) x₃ hx₃ x₂ hx₂ x₁ hx₁ (n + 2) (by simp)
    rw [hc] at h
    exact h
  let e := fullSupportCyclesIso (R := R) (n + 1)
    (show Fintype.card (Option ι) = n + 1 + 1 by simp [hcard])
  have he : e.inv ((optionDeltaIso R ι n).hom (S.X₃.homologyπ n c)) = z := by
    apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
    rw [Iso.inv_hom_id_apply]
    exact hδ
  change S.X₁.iCycles (n + 1)
    (e.inv ((optionDeltaIso R ι n).hom (S.X₃.homologyπ n c))) (optionTuple a) = x₃ a
  rw [he]
  have hzco : S.X₁.iCycles (n + 1) z = x₁ := S.X₁.i_cyclesMk _ _ _ _
  rw [hzco]
  have hf := congrFun hx₁ (optionMiddleTuple a)
  change extendByZero x₁ (optionTuple a).val =
    (complex R (Set.range (@Option.some ι))).d n (n + 1) x₂ (optionMiddleTuple a) at hf
  rw [extendByZero_apply, optionMiddle_d_apply hcard] at hf
  exact hf.trans (congrFun hx₂ a)

end AlgebraicTopology.RelativeSimplex
