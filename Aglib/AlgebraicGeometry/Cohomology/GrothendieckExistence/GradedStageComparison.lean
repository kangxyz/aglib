/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAction
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.QuotientLayerFunctor
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.QuotientLayerLaws

/-! # Original transition compatibility of the common-stage graded construction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- Reducing the common coefficient does not change its original lower quotient. -/
@[reassoc]
theorem baseIdealReductionIso_coefficient_transition {n k m : ℕ}
    (hnk : n ≤ k) (hkm : k ≤ m) :
    idealQuotientHom X (idealThickeningBaseScalar f) (I ^ n)
      (F.obj.map (homOfLE hkm).op) ≫ (baseIdealReductionIso f I F hnk).hom =
        (baseIdealReductionIso f I F (hnk.trans hkm)).hom := by
  apply (cancel_epi (idealQuotientπ X (idealThickeningBaseScalar f)
    (F.obj.obj (op m)) (I ^ n))).mp
  rw [idealQuotientπ_hom_assoc,
    idealQuotientπ_baseIdealReductionIso_hom,
    idealQuotientπ_baseIdealReductionIso_hom, ← F.obj.map_comp]
  congr 1

/-- The common-stage kernel comparison retains its original kernel inclusion. -/
@[reassoc (attr := simp)]
theorem gradedPieceCommonStageIso_hom_ι {n m : ℕ} (h : n + 1 ≤ m) :
    (gradedPieceCommonStageIso f I F h).hom ≫ kernel.ι (F.transition n) =
      kernel.ι (idealQuotientMap X (idealThickeningBaseScalar f)
        (F.obj.obj (op m)) (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)) ≫
        (baseIdealReductionIso f I F h).hom := by
  simp [gradedPieceCommonStageIso]

/-- Original transitions preserve the common-stage description of a successive piece. -/
@[reassoc]
theorem gradedPieceCommonStageIso_transition {n k m : ℕ}
    (hnk : n + 1 ≤ k) (hkm : k ≤ m) :
    idealQuotientLayerHom X (idealThickeningBaseScalar f)
      (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)
      (F.obj.map (homOfLE hkm).op) ≫ (gradedPieceCommonStageIso f I F hnk).hom =
        (gradedPieceCommonStageIso f I F (hnk.trans hkm)).hom := by
  apply (cancel_mono (kernel.ι (F.transition n))).mp
  simp only [Category.assoc, gradedPieceCommonStageIso_hom_ι,
    idealQuotientLayerHom_ι_assoc]
  rw [baseIdealReductionIso_coefficient_transition]

/-- Scalars in the next ideal power act trivially on the original formal graded piece. -/
theorem formalGradedScalarMap_eq_zero (r n : ℕ) (a : ↥(I ^ r))
    (ha : (a : A) ∈ I ^ (r + 1)) : formalGradedScalarMap f I F r n a = 0 := by
  simp [formalGradedScalarMap, idealPowerQuotientLayerMul_eq_zero X
    (idealThickeningBaseScalar f) (F.obj.obj (op (r + n + 1))) I r n a ha]

end AlgebraicGeometry.Scheme.Cohomology
