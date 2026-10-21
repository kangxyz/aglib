/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedStageComparison

/-! # Independence of the common finite stage in formal homogeneous action -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- Compute homogeneous multiplication at any sufficiently high original stage. -/
def formalGradedScalarMapAtStage (r n m : ℕ) (h : r + n + 1 ≤ m) (a : ↥(I ^ r)) :
    F.gradedPiece n ⟶ F.gradedPiece (r + n) :=
  (gradedPieceCommonStageIso f I F
    ((Nat.add_le_add_right (Nat.le_add_left n r) 1).trans h)).inv ≫
    idealPowerQuotientLayerMul X (idealThickeningBaseScalar f)
      (F.obj.obj (op m)) I r n a ≫
    (gradedPieceCommonStageIso f I F h).hom

/-- The original transition squares identify every common-stage computation
with the action defined at the minimal sufficient stage. -/
theorem formalGradedScalarMapAtStage_eq (r n m : ℕ) (h : r + n + 1 ≤ m)
    (a : ↥(I ^ r)) :
    formalGradedScalarMapAtStage f I F r n m h a = formalGradedScalarMap f I F r n a := by
  let hn : n + 1 ≤ r + n + 1 := Nat.add_le_add_right (Nat.le_add_left n r) 1
  let g := F.obj.map (homOfLE h).op
  let sn := idealQuotientLayerHom X (idealThickeningBaseScalar f)
    (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n) g
  let st := idealQuotientLayerHom X (idealThickeningBaseScalar f)
    (Ideal.pow_le_pow_right (Nat.le_succ (r + n)) : I ^ (r + n + 1) ≤ I ^ (r + n)) g
  have hs : sn ≫ (gradedPieceCommonStageIso f I F hn).hom =
      (gradedPieceCommonStageIso f I F (hn.trans h)).hom :=
    gradedPieceCommonStageIso_transition f I F hn h
  have ht : st ≫ (gradedPieceCommonStageIso f I F (le_refl (r + n + 1))).hom =
      (gradedPieceCommonStageIso f I F h).hom :=
    gradedPieceCommonStageIso_transition f I F (le_refl (r + n + 1)) h
  have hmul : sn ≫ idealPowerQuotientLayerMul X (idealThickeningBaseScalar f)
      (F.obj.obj (op (r + n + 1))) I r n a =
      idealPowerQuotientLayerMul X (idealThickeningBaseScalar f)
        (F.obj.obj (op m)) I r n a ≫ st :=
    idealQuotientLayerMul_naturality X (idealThickeningBaseScalar f) g _ _ a _ _
  apply (cancel_epi (gradedPieceCommonStageIso f I F (hn.trans h)).hom).mp
  change (gradedPieceCommonStageIso f I F (hn.trans h)).hom ≫
      (gradedPieceCommonStageIso f I F (hn.trans h)).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  rw [← hs]
  simp only [formalGradedScalarMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hmul, Category.assoc, ht]

end AlgebraicGeometry.Scheme.Cohomology
