/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedHomogeneousAction

/-! # Naturality of the actual formal graded action in the coefficient system -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {F G : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : F ⟶ G)

/-- Original coefficient maps commute with every original common-stage reduction. -/
@[reassoc]
theorem baseIdealReductionIso_naturality {n m : ℕ} (h : n ≤ m) :
    idealQuotientHom X (idealThickeningBaseScalar f) (I ^ n) (φ.hom.app (op m)) ≫
      (baseIdealReductionIso f I G h).hom =
    (baseIdealReductionIso f I F h).hom ≫ φ.hom.app (op n) := by
  apply (cancel_epi (idealQuotientπ X (idealThickeningBaseScalar f)
    (F.obj.obj (op m)) (I ^ n))).mp
  simp only [idealQuotientπ_hom_assoc,
    idealQuotientπ_baseIdealReductionIso_hom,
    idealQuotientπ_baseIdealReductionIso_hom_assoc]
  exact (φ.hom.naturality (homOfLE h).op).symm

/-- Common-stage kernel coordinates preserve the original graded coefficient map. -/
@[reassoc]
theorem gradedPieceCommonStageIso_naturality {n m : ℕ} (h : n + 1 ≤ m) :
    idealQuotientLayerHom X (idealThickeningBaseScalar f)
      (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)
      (φ.hom.app (op m)) ≫ (gradedPieceCommonStageIso f I G h).hom =
    (gradedPieceCommonStageIso f I F h).hom ≫ F.gradedPieceMap φ n := by
  apply (cancel_mono (kernel.ι (G.transition n))).mp
  simp only [Category.assoc, gradedPieceCommonStageIso_hom_ι,
    AdicSystem.gradedPieceMap_ι, gradedPieceCommonStageIso_hom_ι_assoc,
    idealQuotientLayerHom_ι_assoc]
  rw [baseIdealReductionIso_naturality]

/-- Every original formal-system map intertwines finite-stage homogeneous multiplication. -/
@[reassoc]
theorem formalGradedScalarMap_naturality (r n : ℕ) (a : ↥(I ^ r)) :
    F.gradedPieceMap φ n ≫ formalGradedScalarMap f I G r n a =
      formalGradedScalarMap f I F r n a ≫ F.gradedPieceMap φ (r + n) := by
  let hn := Nat.add_le_add_right (Nat.le_add_left n r) 1
  let sn := idealQuotientLayerHom X (idealThickeningBaseScalar f)
    (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)
    (φ.hom.app (op (r + n + 1)))
  let st := idealQuotientLayerHom X (idealThickeningBaseScalar f)
    (Ideal.pow_le_pow_right (Nat.le_succ (r + n)) : I ^ (r + n + 1) ≤ I ^ (r + n))
    (φ.hom.app (op (r + n + 1)))
  have hs : sn ≫ (gradedPieceCommonStageIso f I G hn).hom =
      (gradedPieceCommonStageIso f I F hn).hom ≫ F.gradedPieceMap φ n :=
    gradedPieceCommonStageIso_naturality f I φ hn
  have ht : st ≫ (gradedPieceCommonStageIso f I G (le_refl (r + n + 1))).hom =
      (gradedPieceCommonStageIso f I F (le_refl (r + n + 1))).hom ≫
        F.gradedPieceMap φ (r + n) :=
    gradedPieceCommonStageIso_naturality f I φ (le_refl (r + n + 1))
  have hmul : sn ≫ idealPowerQuotientLayerMul X (idealThickeningBaseScalar f)
      (G.obj.obj (op (r + n + 1))) I r n a =
      idealPowerQuotientLayerMul X (idealThickeningBaseScalar f)
        (F.obj.obj (op (r + n + 1))) I r n a ≫ st :=
    idealQuotientLayerMul_naturality X (idealThickeningBaseScalar f)
      (φ.hom.app (op (r + n + 1))) _ _ a _ _
  apply (cancel_epi (gradedPieceCommonStageIso f I F hn).hom).mp
  rw [← Category.assoc, ← hs]
  simp only [formalGradedScalarMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hmul, Category.assoc, ht]

/-- The native associated-graded homogeneous action is functorial in the formal system. -/
@[reassoc]
theorem formalGradedHomogeneousAction_naturality (r n : ℕ)
    (a : I.associatedGradedGrading r) :
    F.gradedPieceMap φ n ≫ formalGradedHomogeneousAction f I G r n a =
      formalGradedHomogeneousAction f I F r n a ≫ F.gradedPieceMap φ (r + n) := by
  obtain ⟨a, rfl⟩ := I.associatedGradedComponentMap_surjective r a
  simp only [formalGradedHomogeneousAction_componentMap]
  exact formalGradedScalarMap_naturality f I φ r n a

end AlgebraicGeometry.Scheme.Cohomology
