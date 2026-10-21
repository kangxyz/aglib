/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Completion
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Transitions
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.AssociatedGraded
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.QuotientLayers

/-!
# Finite-stage homogeneous action on a formal coefficient

The common-stage comparisons are isomorphisms of the original quotient layers
with the original successive transition kernels. Multiplication is constructed
at stage `r+n+1`; no algebraization or completion is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

local instance coefficient_isQuasicoherent (m : ℕ) :
    (F.obj.obj (op m)).IsQuasicoherent :=
  quasicoherent_of_affineCharts _ (fun R j _ => (F.property.coherent m R j).1)

/-- Reduction from a common finite stage, with the original affine-base quotient. -/
def baseIdealReductionIso {n m : ℕ} (h : n ≤ m) :
    idealPowerQuotient X (idealThickeningBaseScalar f) (F.obj.obj (op m)) I n ≅
      F.obj.obj (op n) :=
  idealPowerQuotientIdealSheafIso f I (F.obj.obj (op m)) n ≪≫ F.reductionIsoOfLE h

@[reassoc (attr := simp)]
theorem idealQuotientπ_baseIdealReductionIso_hom {n m : ℕ} (h : n ≤ m) :
    idealQuotientπ X (idealThickeningBaseScalar f) (F.obj.obj (op m)) (I ^ n) ≫
      (baseIdealReductionIso f I F h).hom = F.obj.map (homOfLE h).op := by
  simp [baseIdealReductionIso]

/-- Common-stage quotient reductions retain all original transition maps. -/
@[reassoc]
theorem baseIdealReductionIso_transition {n k m : ℕ} (hnk : n ≤ k) (hkm : k ≤ m) :
    idealPowerQuotientMap X (idealThickeningBaseScalar f) (F.obj.obj (op m)) I hnk ≫
      (baseIdealReductionIso f I F (hnk.trans hkm)).hom =
    (baseIdealReductionIso f I F hkm).hom ≫ F.obj.map (homOfLE hnk).op := by
  apply (cancel_epi (idealQuotientπ X (idealThickeningBaseScalar f)
    (F.obj.obj (op m)) (I ^ k))).mp
  simp only [idealQuotientπ_map_assoc, idealQuotientπ_baseIdealReductionIso_hom,
    idealQuotientπ_baseIdealReductionIso_hom_assoc]
  rw [← F.obj.map_comp]
  congr 1

/-- A successive piece can be computed at every sufficiently large finite stage. -/
def gradedPieceCommonStageIso {n m : ℕ} (h : n + 1 ≤ m) :
    idealQuotientLayer X (idealThickeningBaseScalar f) (F.obj.obj (op m))
      (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n) ≅
      F.gradedPiece n :=
  kernel.mapIso _ (F.transition n) (baseIdealReductionIso f I F h)
    (baseIdealReductionIso f I F ((Nat.le_succ n).trans h))
    (baseIdealReductionIso_transition f I F (Nat.le_succ n) h)

/-- Homogeneous multiplication on the original formal coefficient, constructed
entirely at the finite common stage `r+n+1`. -/
def formalGradedScalarMap (r n : ℕ) (a : ↥(I ^ r)) :
    F.gradedPiece n ⟶ F.gradedPiece (r + n) :=
  (gradedPieceCommonStageIso f I F
    (Nat.add_le_add_right (Nat.le_add_left n r) 1)).inv ≫
    idealPowerQuotientLayerMul X (idealThickeningBaseScalar f)
      (F.obj.obj (op (r + n + 1))) I r n a ≫
    (gradedPieceCommonStageIso f I F (le_refl (r + n + 1))).hom

end AlgebraicGeometry.Scheme.Cohomology
