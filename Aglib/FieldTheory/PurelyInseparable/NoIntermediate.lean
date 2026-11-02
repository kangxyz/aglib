/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Exponent

/-!
# Algebraic field extensions with no strict intermediate field

The native separable closure and a genuine exponent-one simple subextension
give the separable or purely inseparable prime-degree dichotomy.
-/

@[expose] public noncomputable section

open Module

namespace IntermediateField

/-- With no strict intermediate field, an algebraic field extension is separable
or purely inseparable of prime degree equal to its positive characteristic. -/
theorem separable_or_purelyInseparable_prime_degree
    (F K : Type*) [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (hinter : ∀ L : IntermediateField F K, L = ⊥ ∨ L = ⊤) :
    Algebra.IsSeparable F K ∨
      ∃ p : ℕ, p.Prime ∧ CharP F p ∧ CharP K p ∧
        IsPurelyInseparable F K ∧ Module.finrank F K = p := by
  classical
  by_cases hsep : Algebra.IsSeparable F K
  · exact Or.inl hsep
  right
  have hpure : IsPurelyInseparable F K := by
    rcases hinter (separableClosure F K) with hbot | htop
    · exact separableClosure.eq_bot_iff.mp hbot
    · exact False.elim (hsep ((separableClosure.eq_top_iff F K).mp htop))
  let : IsPurelyInseparable F K := hpure
  have hex : ∃ x : K, x ∉ (algebraMap F K).range := by
    by_contra! h
    apply hsep
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := h x
    exact isSeparable_algebraMap a
  obtain ⟨x, hx⟩ := hex
  obtain ⟨p, hpchar⟩ := ExpChar.exists F
  cases hpchar with
  | zero => exact False.elim (hsep inferInstance)
  | @prime p hp hchar =>
    let : ExpChar F p := .prime hp
    let : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
    let e := IsPurelyInseparable.elemExponent F x
    have he : e ≠ 0 := by
      intro he
      have h := IsPurelyInseparable.elemExponent_def' F p x
      change x ^ p ^ e ∈ (algebraMap F K).range at h
      rw [he, pow_zero, pow_one] at h
      exact hx h
    have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
    let y := x ^ p ^ (e - 1)
    have hy : y ∉ (algebraMap F K).range :=
      IsPurelyInseparable.elemExponent_min' F p (Nat.sub_lt (Nat.pos_of_ne_zero he) (by decide))
    have hyp : y ^ p ∈ (algebraMap F K).range := by
      have h := IsPurelyInseparable.elemExponent_def' F p x
      change x ^ p ^ e ∈ (algebraMap F K).range at h
      dsimp only [y]
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel he1]
      exact h
    have hyexp : IsPurelyInseparable.elemExponent F y = 1 := by
      apply Nat.le_antisymm
      · apply IsPurelyInseparable.elemExponent_le_of_pow_mem' p
        simpa only [pow_one] using hyp
      · apply Nat.one_le_iff_ne_zero.mpr
        intro hzero
        have h := IsPurelyInseparable.elemExponent_def' F p y
        rw [hzero, pow_zero, pow_one] at h
        exact hy h
    have hdeg : Module.finrank F (IntermediateField.adjoin F {y}) = p := by
      rw [IntermediateField.adjoin.finrank (IsPurelyInseparable.isIntegral' F y),
        IsPurelyInseparable.minpoly_natDegree_eq' F p y, hyexp, pow_one]
    have htop : IntermediateField.adjoin F {y} = ⊤ := by
      rcases hinter (IntermediateField.adjoin F {y}) with hbot | htop
      · have hm : y ∈ IntermediateField.adjoin F {y} :=
          IntermediateField.subset_adjoin F {y} (Set.mem_singleton y)
        rw [hbot, IntermediateField.mem_bot] at hm
        exact False.elim (hy hm)
      · exact htop
    refine ⟨p, hp, hchar, inferInstance, hpure, ?_⟩
    exact (IntermediateField.finrank_top' (F := F) (E := K)).symm.trans
      ((congrArg (fun L : IntermediateField F K => Module.finrank F L) htop).symm.trans hdeg)

end IntermediateField
