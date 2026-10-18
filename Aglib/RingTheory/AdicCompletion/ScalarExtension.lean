/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Completion for an extended ideal

Restriction of scalars identifies the actual quotient systems, and hence the completions,
for an ideal and its extension to an algebra.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace AdicCompletion

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module S M] [Module R M]
  [IsScalarTower R S M]

/-- The literal scalar-restriction equivalence of the quotients in the two filtrations. -/
def mapIdealQuotientEquiv (n : ℕ) :
    (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃ₗ[R]
      M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq]
    rfl)).trans (Submodule.Quotient.restrictScalarsEquiv R _)

@[simp] theorem mapIdealQuotientEquiv_mk (n : ℕ) (x : M) :
    mapIdealQuotientEquiv (S := S) I M n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  simp [mapIdealQuotientEquiv]

/-- The quotient comparisons commute with every transition map. -/
theorem mapIdealQuotientEquiv_transition {m n : ℕ} (h : m ≤ n)
    (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    mapIdealQuotientEquiv (S := S) I M m (transitionMap I M h x) =
      transitionMap (I.map (algebraMap R S)) M h (mapIdealQuotientEquiv (S := S) I M n x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp [transitionMap, Submodule.factorPow]

/-- Completion for an ideal and for its extension have the same actual elements. -/
def mapIdealLinearEquiv :
    AdicCompletion I M ≃ₗ[R] AdicCompletion (I.map (algebraMap R S)) M where
  toFun x := ⟨fun n ↦ mapIdealQuotientEquiv (S := S) I M n (x.val n), fun {m n} h ↦ by
    rw [← mapIdealQuotientEquiv_transition I M h, x.prop h]⟩
  invFun y := ⟨fun n ↦ (mapIdealQuotientEquiv (S := S) I M n).symm (y.val n), fun {m n} h ↦ by
    apply (mapIdealQuotientEquiv (S := S) I M m).injective
    rw [mapIdealQuotientEquiv_transition (S := S)]
    simp only [LinearEquiv.apply_symm_apply, y.prop h]⟩
  left_inv x := by ext n; exact LinearEquiv.symm_apply_apply _ _
  right_inv y := by ext n; exact LinearEquiv.apply_symm_apply _ _
  map_add' x y := by ext n; exact map_add _ _ _
  map_smul' r x := by ext n; exact (mapIdealQuotientEquiv (S := S) I M n).map_smul r (x.val n)

@[simp] theorem mapIdealLinearEquiv_of (x : M) :
    mapIdealLinearEquiv (S := S) I M (of I M x) = of (I.map (algebraMap R S)) M x := by
  ext n
  exact mapIdealQuotientEquiv_mk I M n x

end AdicCompletion
