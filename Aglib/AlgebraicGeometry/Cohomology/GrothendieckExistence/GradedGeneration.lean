/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAction

/-!
# Ideal-image description of original formal graded pieces

Each degree-n piece is the original image of I^n acting on F_(n+1), without
any algebraization. The comparison keeps the actual ideal inclusion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The original base ideal power annihilates its original formal level. -/
theorem formalCoefficient_scalar_eq_zero (n : ℕ) (a : ↥(I ^ n)) :
    globalScalarEndomorphism X (F.obj.obj (op n)) (idealThickeningBaseScalar f a) = 0 := by
  let e := baseIdealReductionIso f I F (le_refl n)
  apply (cancel_epi e.hom).mp
  rw [comp_zero]
  have h := (globalScalarCenter X (idealThickeningBaseScalar f a)).naturality e.hom
  change e.hom ≫ globalScalarEndomorphism X _ (idealThickeningBaseScalar f a) =
    globalScalarEndomorphism X _ (idealThickeningBaseScalar f a) ≫ e.hom at h
  rw [h, idealQuotient_scalar_eq_zero, zero_comp]

/-- The original ideal-multiple inclusion is a kernel of the original transition. -/
def formalIdealMultipleIsKernel (n : ℕ) :
    IsLimit (KernelFork.ofι
      (idealMultipleι X (idealThickeningBaseScalar f) (F.obj.obj (op (n + 1))) (I ^ n))
      (show idealMultipleι X (idealThickeningBaseScalar f)
          (F.obj.obj (op (n + 1))) (I ^ n) ≫ F.transition n = 0 by
        change idealMultipleι X (idealThickeningBaseScalar f)
          (F.obj.obj (op (n + 1))) (I ^ n) ≫ F.obj.map (homOfLE (Nat.le_succ n)).op = 0
        rw [← idealQuotientπ_baseIdealReductionIso_hom f I F (Nat.le_succ n),
          ← Category.assoc, idealMultipleι_quotientπ, zero_comp])) := by
  let e := baseIdealReductionIso f I F (Nat.le_succ n)
  have he : F.transition n ≫ e.inv =
      idealQuotientπ X (idealThickeningBaseScalar f) (F.obj.obj (op (n + 1))) (I ^ n) := by
    change F.obj.map (homOfLE (Nat.le_succ n)).op ≫ e.inv = _
    calc
      _ = (idealQuotientπ X (idealThickeningBaseScalar f)
          (F.obj.obj (op (n + 1))) (I ^ n) ≫ e.hom) ≫ e.inv :=
        congrArg (fun k => k ≫ e.inv)
          (idealQuotientπ_baseIdealReductionIso_hom f I F (Nat.le_succ n)).symm
      _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let : Mono (idealSequence X (idealThickeningBaseScalar f)
    (F.obj.obj (op (n + 1))) (I ^ n)).f :=
    (idealSequence_shortExact X (idealThickeningBaseScalar f)
      (F.obj.obj (op (n + 1))) (I ^ n)).mono_f
  exact IsKernel.ofCompIso _ (F.transition n) e.symm he
    (idealSequence_shortExact X (idealThickeningBaseScalar f)
      (F.obj.obj (op (n + 1))) (I ^ n)).exact.fIsKernel

set_option backward.defeqAttrib.useBackward true in
/-- Each original graded piece is the original ideal-power image at its finite stage. -/
def formalIdealMultipleGradedPieceIso (n : ℕ) :
    idealPower X (idealThickeningBaseScalar f) (F.obj.obj (op (n + 1))) I n ≅
      F.gradedPiece n :=
  (formalIdealMultipleIsKernel f I F n).conePointUniqueUpToIso
    (limit.isLimit (parallelPair (F.transition n) 0))

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
theorem formalIdealMultipleGradedPieceIso_hom_ι (n : ℕ) :
    (formalIdealMultipleGradedPieceIso f I F n).hom ≫ kernel.ι (F.transition n) =
      idealMultipleι X (idealThickeningBaseScalar f) (F.obj.obj (op (n + 1))) (I ^ n) :=
  (formalIdealMultipleIsKernel f I F n).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (parallelPair (F.transition n) 0)) WalkingParallelPair.zero

end AlgebraicGeometry.Scheme.Cohomology
