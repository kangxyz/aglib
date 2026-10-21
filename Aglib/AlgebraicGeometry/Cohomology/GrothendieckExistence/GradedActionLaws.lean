/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedStageIndependence
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedDegreeZero

/-! # Unit and multiplication laws for the original finite-stage graded action -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The homogeneous unit acts as the identity, with the native degree transport. -/
theorem formalGradedScalarMap_one (n : ℕ) :
    HEq (formalGradedScalarMap f I F 0 n ⟨1, by simp⟩) (𝟙 (F.gradedPiece n)) := by
  apply (formalGradedScalarMap_degreeZero f I F n 1).trans
  apply heq_of_eq
  simp [globalScalarEndomorphism]

/-- Multiplication is composition on a common original stage. The heterogeneous
form records only the unavoidable associativity transport of the degree. -/
theorem formalGradedScalarMap_mul (r s n : ℕ) (a : ↥(I ^ r)) (b : ↥(I ^ s)) :
    HEq (formalGradedScalarMap f I F s n b ≫
      formalGradedScalarMap f I F r (s + n) a)
      (formalGradedScalarMap f I F (r + s) n
        ⟨(a : A) * b, by rw [pow_add]; exact Ideal.mul_mem_mul a.property b.property⟩) := by
  let m := r + (s + n) + 1
  have hs : s + n + 1 ≤ m := by dsimp [m]; omega
  have ht : (r + s) + n + 1 ≤ m := by dsimp [m]; omega
  rw [← formalGradedScalarMapAtStage_eq f I F s n m hs b,
    ← formalGradedScalarMapAtStage_eq f I F (r + s) n m ht]
  simp only [formalGradedScalarMapAtStage, formalGradedScalarMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  unfold idealPowerQuotientLayerMul
  rw [← Category.assoc (idealQuotientLayerMul _ _ _ _ _ _ _ _),
    idealQuotientLayerMul_comp]
  let hsource : n + 1 ≤ m := by dsimp [m]; omega
  let C (t : ℕ) (ht : t + 1 ≤ m) (hd : t = (r + s) + n) :
      F.gradedPiece n ⟶ F.gradedPiece t :=
    (gradedPieceCommonStageIso f I F hsource).inv ≫
      idealQuotientLayerMul X (idealThickeningBaseScalar f) (F.obj.obj (op m))
        (Ideal.pow_le_pow_right (Nat.le_succ n))
        (Ideal.pow_le_pow_right (Nat.le_succ t)) ((a : A) * b)
        (fun x hx => by
          change ((a : A) * b) * x ∈ I ^ (t + 1)
          rw [hd, show (r + s) + n + 1 = (r + s) + (n + 1) from
            Nat.add_assoc (r + s) n 1, pow_add]
          apply Ideal.mul_mem_mul
          · rw [pow_add]; exact Ideal.mul_mem_mul a.property b.property
          · exact hx)
        (fun x hx => by
          rw [hd, pow_add]
          apply Ideal.mul_mem_mul
          · rw [pow_add]; exact Ideal.mul_mem_mul a.property b.property
          · exact hx) ≫ (gradedPieceCommonStageIso f I F ht).hom
  have hC (t t' : ℕ) (ht : t + 1 ≤ m) (ht' : t' + 1 ≤ m)
      (hd : t = (r + s) + n) (hd' : t' = (r + s) + n) (h : t = t') :
      HEq (C t ht hd) (C t' ht' hd') := by
    cases h
    rfl
  change HEq (C (r + (s + n)) (le_refl m) (Nat.add_assoc r s n).symm)
    (C ((r + s) + n) ht rfl)
  exact hC (r + (s + n)) ((r + s) + n) (le_refl m) ht
    (Nat.add_assoc r s n).symm rfl (Nat.add_assoc r s n).symm

end AlgebraicGeometry.Scheme.Cohomology
