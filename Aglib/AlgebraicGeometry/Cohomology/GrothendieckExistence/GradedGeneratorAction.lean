/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedGenerators
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedStageComparison

/-! # The first-level generators are the original homogeneous action -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The actual finite-stage scalar generators coincide with the actual graded action,
with only the unavoidable transport along `n+0=n`. -/
theorem formalGradedScalarMap_generator (n : ℕ) (a : ↥(I ^ n)) :
    HEq (formalGradedScalarMap f I F n 0 a)
      (F.gradedPieceZeroIso.hom ≫ formalGradedPieceGenerator f I F n a) := by
  let M := F.obj.obj (op (n + 1))
  let α := idealThickeningBaseScalar f
  let h0 : I ^ (0 + 1) ≤ I ^ 0 := Ideal.pow_le_pow_right (Nat.le_succ 0)
  let e := gradedPieceCommonStageIso f I F (Nat.succ_le_succ (Nat.zero_le n))
  let k : M ⟶ idealQuotientLayer X α M h0 :=
    kernel.lift _ (idealQuotientπ X α M (I ^ (0 + 1))) (by
      rw [idealQuotientπ_map]
      exact (idealPowerQuotient_zero_isZero X α M I).eq_of_tgt _ _)
  have hk0 : k ≫ kernel.ι (idealQuotientMap X α M h0) =
      idealQuotientπ X α M (I ^ (0 + 1)) := kernel.lift_ι _ _ _
  have hk : k ≫ e.hom ≫ F.gradedPieceZeroIso.hom =
      F.obj.map (homOfLE (Nat.succ_le_succ (Nat.zero_le n))).op := by
    rw [F.gradedPieceZeroIso_hom]
    rw [show e.hom ≫ kernel.ι (F.transition 0) =
      kernel.ι (idealQuotientMap X α M h0) ≫
        (baseIdealReductionIso f I F (Nat.succ_le_succ (Nat.zero_le n))).hom from
          gradedPieceCommonStageIso_hom_ι f I F _]
    rw [← Category.assoc, hk0, idealQuotientπ_baseIdealReductionIso_hom]
  have : Epi (k ≫ e.hom) := by
    have : Epi ((k ≫ e.hom) ≫ F.gradedPieceZeroIso.hom) := by
      rw [Category.assoc, hk]
      infer_instance
    exact (epi_comp_iff_of_isIso _ F.gradedPieceZeroIso.hom).mp inferInstance
  apply heq_of_eq
  change e.inv ≫ idealPowerQuotientLayerMul X α M I n 0 a ≫
    (gradedPieceCommonStageIso f I F (le_refl (n + 1))).hom = _
  apply (cancel_epi (k ≫ e.hom)).mp
  apply (cancel_mono (kernel.ι (F.transition n))).mp
  have hr : k ≫ e.hom ≫ F.gradedPieceZeroIso.hom ≫
      formalGradedPieceGenerator f I F n a ≫ kernel.ι (F.transition n) =
      globalScalarEndomorphism X M (α a) := by
    rw [reassoc_of% hk, formalGradedPiece_transition_generator_assoc]
    simp only [formalGradedPieceScalar, Category.assoc,
      formalIdealMultipleGradedPieceIso_hom_ι, idealMultipleScalar_ι]
    rfl
  have ht := gradedPieceCommonStageIso_hom_ι f I F (le_refl (n + 1))
  change (k ≫ e.hom) ≫ (e.inv ≫ idealPowerQuotientLayerMul X α M I n 0 a ≫
    (gradedPieceCommonStageIso f I F (le_refl (n + 1))).hom) ≫
      kernel.ι (F.transition n) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [ht]
  have hmul : idealPowerQuotientLayerMul X α M I n 0 a ≫
      kernel.ι (idealQuotientMap X α M
        (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)) =
      kernel.ι (idealQuotientMap X α M h0) ≫
        idealQuotientMul X α M (a : A) (fun b hb => by
          rw [pow_add]
          exact Ideal.mul_mem_mul a.property hb) := by
    exact idealQuotientLayerMul_ι X α M _ _ _ _ _
  rw [reassoc_of% hmul]
  rw [← Category.assoc k, hk0]
  rw [idealQuotientπ_mul_assoc]
  have hid : idealQuotientπ X α M (I ^ (n + 1)) ≫
      (baseIdealReductionIso f I F (le_refl (n + 1))).hom = 𝟙 M := by
    exact (idealQuotientπ_baseIdealReductionIso_hom f I F
      (le_refl (n + 1))).trans (F.obj.map_id (op (n + 1)))
  rw [hid, Category.comp_id]
  exact hr.symm

end AlgebraicGeometry.Scheme.Cohomology
