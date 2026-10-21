/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystem
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# One finite family generating every stage of a compatible system

Choose a finite free presentation of the first nonzero stage and lift it through
the native limit projection. Nilpotent Nakayama then proves that the same lifted
family generates every stage. This does not yet assert that it generates the
inverse limit over the original, possibly incomplete ring.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u v w z

namespace Submodule

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Nilpotent Nakayama needs no finiteness hypothesis. -/
theorem eq_top_of_sup_smul_eq_top_of_pow_smul_eq_bot (N : Submodule R M) (I : Ideal R)
    (h : N ⊔ I • (⊤ : Submodule R M) = ⊤)
    (k : ℕ) (hk : I ^ k • (⊤ : Submodule R M) = ⊥) : N = ⊤ := by
  have hall : ∀ n : ℕ, N ⊔ I ^ n • (⊤ : Submodule R M) = ⊤ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      apply top_le_iff.mp
      apply le_trans h.ge
      apply sup_le le_sup_left
      calc
        I • (⊤ : Submodule R M) = I • (N ⊔ I ^ n • (⊤ : Submodule R M)) := by rw [ih]
        _ = I • N ⊔ I ^ (n + 1) • (⊤ : Submodule R M) := by
          rw [Submodule.smul_sup, pow_succ', mul_smul]
        _ ≤ N ⊔ I ^ (n + 1) • (⊤ : Submodule R M) :=
          sup_le_sup Submodule.smul_le_right le_rfl
  simpa only [hk, sup_bot_eq] using hall k

end Submodule

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {P : Type v} {M : Type w} {N : Type z}
variable [AddCommGroup P] [AddCommGroup M] [AddCommGroup N]
variable [Module R P] [Module R M] [Module R N]

/-- A family surjective modulo a nilpotent ideal already generates the module. -/
theorem surjective_of_surjective_comp_of_ker_le_smul
    (I : Ideal R) (g : P →ₗ[R] M) (t : M →ₗ[R] N)
    (htg : Function.Surjective (t.comp g))
    (hker : t.ker ≤ I • (⊤ : Submodule R M))
    (k : ℕ) (hk : I ^ k • (⊤ : Submodule R M) = ⊥) : Function.Surjective g := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_sup_smul_eq_top_of_pow_smul_eq_bot g.range I _ k hk
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hy⟩ := htg (t x)
  have hz : x - g y ∈ I • (⊤ : Submodule R M) := by
    apply hker
    change t (x - g y) = 0
    rw [map_sub, ← LinearMap.comp_apply, hy, sub_self]
  have : g y + (x - g y) ∈ g.range ⊔ I • (⊤ : Submodule R M) :=
    Submodule.add_mem _
      ((show g.range ≤ g.range ⊔ I • (⊤ : Submodule R M) from le_sup_left)
        (LinearMap.mem_range_self g y))
      ((show I • (⊤ : Submodule R M) ≤ g.range ⊔ I • ⊤ from le_sup_right) hz)
  have he : g y + (x - g y) = x := by rw [add_comm, sub_add_cancel]
  rwa [he] at this

end LinearMap

namespace AdicCompletion.IsCompatibleSystem

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} (hF : IsCompatibleSystem I F)

include hF

/-- The defining ideal power annihilates the entire stage module. -/
theorem pow_smul_top_eq_bot (n : ℕ) :
    I ^ n • (⊤ : Submodule R (F.obj (op n))) = ⊥ := by
  apply le_bot_iff.mp
  apply Submodule.smul_le.mpr
  intro a ha x _
  exact hF.annihilated n ⟨a, ha⟩ x

/-- Compatible lifts which generate the first nonzero stage generate every stage. -/
theorem sectionsEval_comp_surjective_of_one
    {P : Type w} [AddCommGroup P] [Module R P]
    (g : P →ₗ[R] ModuleCat.sectionsSubmodule F)
    (hg : Function.Surjective ((ModuleCat.sectionsEval F 1).comp g)) (n : ℕ) :
    Function.Surjective ((ModuleCat.sectionsEval F n).comp g) := by
  have hs : ∀ n : ℕ, Function.Surjective ((ModuleCat.sectionsEval F (n + 1)).comp g) := by
    intro n
    induction n with
    | zero => exact hg
    | succ n ih =>
      apply LinearMap.surjective_of_surjective_comp_of_ker_le_smul I
        ((ModuleCat.sectionsEval F (n + 1 + 1)).comp g)
        (F.map (homOfLE (Nat.le_succ (n + 1))).op).hom _ _ (n + 1 + 1)
        (hF.pow_smul_top_eq_bot (n + 1 + 1))
      · convert ih using 1
        congr 1
        ext x
        exact ModuleCat.map_sectionsEval F (Nat.le_succ (n + 1)) (g x)
      · rw [hF.ker_transition]
        exact Submodule.smul_mono (Ideal.pow_le_self (by omega)) le_rfl
  cases n with
  | zero =>
    intro x
    exact ⟨0, by simpa only [map_zero] using (hF.zero_eq x).symm⟩
  | succ n => exact hs n

/-- One finite free module maps compatibly onto every stage through the actual
native inverse-limit module. The limit need not be finite over `R`. -/
theorem exists_finite_free_generators :
    ∃ (r : ℕ) (g : (Fin r → R) →ₗ[R] ModuleCat.sectionsSubmodule F),
      ∀ n : ℕ, Function.Surjective ((ModuleCat.sectionsEval F n).comp g) := by
  let := hF.finite 1
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' R (F.obj (op 1))
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (ModuleCat.sectionsEval F 1) f
    (hF.sectionsEval_surjective 1)
  refine ⟨r, g, fun n => hF.sectionsEval_comp_surjective_of_one g ?_ n⟩
  rwa [hg]

end AdicCompletion.IsCompatibleSystem
