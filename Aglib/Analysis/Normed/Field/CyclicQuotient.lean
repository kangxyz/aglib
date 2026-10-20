/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.FieldTheory.Units.CyclicQuotientDescent
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Small norm consequences for cyclic unit quotients

Sources: `R5Lab.Aglib.FieldTheory.Units.CyclicQuotient` and
`R5Lab.Aglib.FieldTheory.Units.CyclicQuotientDescent`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section

universe u v

namespace Units.CyclicQuotient

section Normed
variable {K : Type u} [NormedField K]

/-- The actual norm makes a small unit an infinite-order period. -/
theorem unit_orderOf_eq_zero_of_norm_lt_one (q : Kˣ) (hqn : ‖(q : K)‖ < 1) :
    orderOf q = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn h
  have hnrm := congrArg (fun x : Kˣ => ‖(x : K)‖) h
  have hlt : ‖(q : K)‖ ^ n < 1 := pow_lt_one₀ (norm_nonneg _) hqn (by omega)
  simp only [Units.val_pow_eq_pow_val, Units.val_one, norm_pow, norm_one] at hnrm
  exact (ne_of_lt hlt) hnrm

variable {q : Kˣ} {hq : Function.Injective (fun z : ℤ => q ^ z)}
  {H : Subgroup (QuotientGroup.CyclicQuotient q)}

namespace KernelNormalForm

/-- The new period is an actual small unit in the same normed field. -/
theorem norm_p_lt_one (N : KernelNormalForm q hq H) [Finite H]
    (hqn : ‖(q : K)‖ < 1) : ‖(N.p : K)‖ < 1 := by
  have hnorm := congrArg (fun x : Kˣ => ‖(x : K)‖) N.power_relation
  simp only [Units.val_pow_eq_pow_val, norm_pow] at hnorm
  apply (pow_lt_one_iff_of_nonneg (norm_nonneg _) N.b_pos.ne').mp
  rw [← hnorm]
  exact pow_lt_one₀ (norm_nonneg _) hqn N.a_pos.ne'

theorem p_orderOf_eq_zero (N : KernelNormalForm q hq H) [Finite H]
    (hqn : ‖(q : K)‖ < 1) : orderOf N.p = 0 :=
  unit_orderOf_eq_zero_of_norm_lt_one N.p (N.norm_p_lt_one hqn)

/-- The order of the given finite subgroup is derived from the actual kernel
equality and the previously proved geometric lattice-map cardinality. -/
theorem card_eq [IsAlgClosed K] [CharZero K]
    (N : KernelNormalForm q hq H) [Finite H] (hqn : ‖(q : K)‖ < 1) :
    Nat.card H = N.a * N.b := by
  calc
    Nat.card H = Nat.card (QuotientGroup.zpowersPowerMap q N.p N.a N.b N.power_relation).ker :=
      congrArg (fun J : Subgroup (QuotientGroup.CyclicQuotient q) => Nat.card J) N.actual_kernel
    _ = N.a * N.b := QuotientGroup.zpowersPowerMap_units_kernel_card K q N.p N.a N.b N.a_pos
      (unit_orderOf_eq_zero_of_norm_lt_one q hqn) (N.p_orderOf_eq_zero hqn) N.power_relation

end KernelNormalForm

/-- Power injectivity follows from the actual parameter's norm. -/
theorem smallUnitPowerInjective (q : Kˣ) (hqn : ‖(q : K)‖ < 1) :
    Function.Injective (fun z : ℤ => q ^ z) :=
  injective_zpow_iff_not_isOfFinOrder.mpr
    (orderOf_eq_zero_iff.mp (unit_orderOf_eq_zero_of_norm_lt_one q hqn))

/-- The normal form is constructed from the original finite subgroup and norm;
no integer generator, minimum, roots-of-unity kernel or map is an input. -/
def finiteSubgroupNormalForm (q : Kˣ) (hqn : ‖(q : K)‖ < 1)
    (H : Subgroup (QuotientGroup.CyclicQuotient q)) [Finite H] :
    KernelNormalForm q (smallUnitPowerInjective q hqn) H :=
  kernelNormalForm q (smallUnitPowerInjective q hqn) H

/-- Literal quotient-group finite-kernel classification, with positivity, a
small output period, the exact power relation, actual kernel equality and
cardinality all produced by the construction. This is not scheme-kernel or
incoming-isogeny classification. -/
theorem finite_subgroup_is_lattice_kernel [IsAlgClosed K] [CharZero K]
    (q : Kˣ) (hqn : ‖(q : K)‖ < 1)
    (H : Subgroup (QuotientGroup.CyclicQuotient q)) [Finite H] :
    ∃ (a b : ℕ) (p : Kˣ), 0 < a ∧ 0 < b ∧ ‖(p : K)‖ < 1 ∧
      ∃ hrel : q ^ a = p ^ b,
        H = (QuotientGroup.zpowersPowerMap q p a b hrel).ker ∧ Nat.card H = a * b := by
  let N := finiteSubgroupNormalForm q hqn H
  exact ⟨N.a, N.b, N.p, N.a_pos, N.b_pos, N.norm_p_lt_one hqn,
    N.power_relation, N.actual_kernel, N.card_eq hqn⟩

end Normed

section Normed
variable {F : Type u} {K : Type v} [NormedField F] [Field K] [Algebra F K]
  [IsAlgClosed K] [CharZero F]
  (q : Fˣ)
  (hq : Function.Injective (fun z : ℤ => (Units.map (algebraMap F K).toMonoidHom q) ^ z))
  (H : Subgroup (QuotientGroup.CyclicQuotient (Units.map (algebraMap F K).toMonoidHom q)))
    [Finite H]
  (N : KernelNormalForm (Units.map (algebraMap F K).toMonoidHom q) hq H)
  (hstable : AlgebraicSubgroupStable q H)

/-- Smallness follows in F from the descended power relation and positive
exponents. No norm comparison between F and the ambient field is an input. -/
theorem KernelNormalForm.norm_originalPeriod_lt_one (hqn : ‖(q : F)‖ < 1) :
    ‖(N.originalPeriod q hq H hstable : F)‖ < 1 := by
  have hnorm := congrArg (fun x : Fˣ => ‖(x : F)‖)
    (N.originalPeriod_relation q hq H hstable)
  simp only [Units.val_pow_eq_pow_val, norm_pow] at hnorm
  apply (pow_lt_one_iff_of_nonneg (norm_nonneg _) N.b_pos.ne').mp
  rw [← hnorm]
  exact pow_lt_one₀ (norm_nonneg _) hqn N.a_pos.ne'

end Normed

end Units.CyclicQuotient
