/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystem

/-! # Compatible systems from original quotient coordinates

All-order quotient coordinates retaining the original transition maps imply
native compatibility. No additional kernel or cartesian relation system is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AdicCompletion
universe u v
variable {B : Type u} [CommRing B] (J : Ideal B)
  (S : ℕᵒᵖ ⥤ ModuleCat.{v} B)

/-- All-order original quotient coordinates imply native compatibility.
The diagonal order supplies annihilation, so it is not added as a hidden input. -/
theorem isCompatibleSystem_of_originalQuotientEquiv
    (hfinite : ∀ n : ℕ, Module.Finite B (S.obj (op n)))
    (e : ∀ {n m : ℕ}, n ≤ m →
      (S.obj (op m) ⧸ (J ^ n • (⊤ : Submodule B (S.obj (op m))))) ≃ₗ[B]
        S.obj (op n))
    (he : ∀ {n m : ℕ} (h : n ≤ m) (x : S.obj (op m)),
      e h (Submodule.Quotient.mk x) = S.map (homOfLE h).op x) :
    IsCompatibleSystem J S := by
  have hker {n m : ℕ} (h : n ≤ m) :
      (S.map (homOfLE h).op).hom.ker =
        J ^ n • (⊤ : Submodule B (S.obj (op m))) := by
    ext x
    change S.map (homOfLE h).op x = 0 ↔ _
    rw [← he h x, ← (e h).map_zero]
    exact (e h).injective.eq_iff.trans (Submodule.Quotient.mk_eq_zero _)
  refine ⟨hfinite, ?_, ?_, fun n => hker (Nat.le_succ n)⟩
  · intro n a x
    have hx : (a : B) • x ∈ J ^ n • (⊤ : Submodule B (S.obj (op n))) :=
      Submodule.smul_mem_smul a.property (Submodule.mem_top : x ∈ (⊤ : Submodule B _))
    rw [← hker (le_refl n)] at hx
    simpa using hx
  · intro n y
    obtain ⟨q, hq⟩ := (e (Nat.le_succ n)).surjective y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨x, (he (Nat.le_succ n) x).symm.trans hq⟩

end AdicCompletion
