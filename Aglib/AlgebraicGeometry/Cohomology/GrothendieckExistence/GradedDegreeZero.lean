/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAction
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.QuotientScalar

/-! # The degree-zero action is the original structural scalar action -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- Every degree-zero scalar acts by the original structural endomorphism,
including the native transport along `0+n=n`. -/
theorem formalGradedScalarMap_degreeZero (n : ℕ) (a : A) :
    HEq (formalGradedScalarMap f I F 0 n ⟨a, by simp⟩)
      (globalScalarEndomorphism X (F.gradedPiece n) (idealThickeningBaseScalar f a)) := by
  let e := gradedPieceCommonStageIso f I F (le_refl (n + 1))
  let h : I ^ (n + 1) ≤ I ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
  have hc : HEq (formalGradedScalarMap f I F 0 n ⟨a, by simp⟩)
      (e.inv ≫ idealQuotientLayerMul X (idealThickeningBaseScalar f)
        (F.obj.obj (op (n + 1))) h h a
        (fun _ hb => (I ^ (n + 1)).mul_mem_left a hb)
        (fun _ hb => (I ^ n).mul_mem_left a hb) ≫ e.hom) := by
    unfold formalGradedScalarMap idealPowerQuotientLayerMul
    dsimp [e, h]
    congr! <;> omega
  apply hc.trans
  apply heq_of_eq
  rw [idealQuotientLayerMul_self]
  have hn : globalScalarEndomorphism X _ (idealThickeningBaseScalar f a) ≫ e.hom =
      e.hom ≫ globalScalarEndomorphism X (F.gradedPiece n) (idealThickeningBaseScalar f a) :=
    ((globalScalarCenter X (idealThickeningBaseScalar f a)).naturality e.hom).symm
  rw [hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end AlgebraicGeometry.Scheme.Cohomology
