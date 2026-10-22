/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Scalar descent for bounded torsion over a completion

A finite module over the completion is finite over the original ring if a
power of the defining ideal kills it. This statement deliberately does not
apply to torsion for an unrelated ideal.
-/

@[expose] public section

namespace Module.Finite

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Finite generation descends when each scalar action can be represented
by an original scalar. Surjectivity of the ring map is not required. -/
theorem of_scalar_actions_lift [Module.Finite S M]
    (h : ∀ s : S, ∃ r : R, ∀ m : M, s • m = r • m) : Module.Finite R M := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := M)
  have hle : (Submodule.span S (s : Set M)).restrictScalars R ≤
      Submodule.span R (s : Set M) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨r, hr⟩ := h a
      rw [hr y]
      exact Submodule.smul_mem _ r hy
  refine ⟨⟨s, eq_top_iff.mpr ?_⟩⟩
  simpa only [hs, Submodule.restrictScalars_top] using hle

end Module.Finite

namespace IsAdicComplete

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A module killed by one ideal power is complete: its adic filtration is
eventually zero. No finite-generation or Noetherian hypothesis is needed. -/
theorem of_pow_smul_eq_bot (I : Ideal R) (t : ℕ)
    (hM : I ^ t • (⊤ : Submodule R M) = ⊥) : IsAdicComplete I M where
  haus' x hx := by
    have h := SModEq.zero.mp (hx t)
    rw [hM] at h
    exact h
  prec' f hf := by
    refine ⟨f t, fun n => ?_⟩
    rcases le_total n t with h | h
    · exact hf h
    · have heq : f t = f n := by
        simpa only [hM, SModEq.bot] using hf h
      rw [heq]

end IsAdicComplete

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
  [Module (AdicCompletion I R) M] [IsScalarTower R (AdicCompletion I R) M]

/-- On a bounded-torsion module, every completed scalar acts as an original
scalar. The bound uses the same ideal as the completion. -/
theorem scalar_action_lifts_of_pow_smul_eq_bot (hI : I.FG) (t : ℕ)
    (hM : I ^ t • (⊤ : Submodule R M) = ⊥) (s : AdicCompletion I R) :
    ∃ r : R, ∀ m : M, s • m = r • m := by
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (eval I R t s)
  have hdiff : s - of I R r ∈ I ^ t • (⊤ : Submodule R (AdicCompletion I R)) := by
    rw [pow_smul_top_eq_ker_eval (M := R) hI]
    change eval I R t (s - of I R r) = 0
    rw [map_sub, eval_of, ← hr]
    exact sub_self _
  refine ⟨r, fun m => ?_⟩
  have hz : (s - of I R r) • m = 0 := by
    refine Submodule.smul_induction_on hdiff (fun a ha b _ => ?_)
      (fun a b ha hb => by rw [add_smul, ha, hb, add_zero])
    rw [smul_assoc]
    have hm := Submodule.smul_mem_smul ha (Submodule.mem_top : b • m ∈ (⊤ : Submodule R M))
    rw [hM] at hm
    exact hm
  rw [sub_smul, sub_eq_zero] at hz
  change s • m = (algebraMap R (AdicCompletion I R) r) • m at hz
  simpa only [algebraMap_smul] using hz

/-- Bounded torsion, unlike arbitrary completed finiteness, permits descent
of finite generation to the uncompleted ring. -/
theorem finite_of_pow_smul_eq_bot (hI : I.FG) (t : ℕ)
    [Module.Finite (AdicCompletion I R) M]
    (hM : I ^ t • (⊤ : Submodule R M) = ⊥) : Module.Finite R M :=
  Module.Finite.of_scalar_actions_lift
    (scalar_action_lifts_of_pow_smul_eq_bot I hI t hM)

end AdicCompletion
