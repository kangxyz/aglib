/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.Basic
public import Aglib.RingTheory.TensorProduct.CoordinateModuleBijective
public import Mathlib.Algebra.DirectSum.Module

/-! # Scalar extension in the native associated-graded coordinate square -/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

namespace Ideal

variable {A : Type*} [CommRing A] (I : Ideal A)
  (B D : Type*) [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D] [Algebra B D] [IsScalarTower A B D]

/-- The associated-graded coefficient ring retains its native ideal-quotient operations. -/
local instance : CommRing I.associatedGraded := Ideal.Quotient.commRing I.associatedGradedIdeal

/-- The tensor-coordinate comparison uses the original coordinate algebra action. -/
local instance : Algebra (B ⊗[A] I.associatedGraded) (D ⊗[A] I.associatedGraded) :=
  Algebra.TensorProduct.coordinateAlgebra A B D I.associatedGraded
local instance : IsScalarTower B (B ⊗[A] I.associatedGraded) (D ⊗[A] I.associatedGraded) :=
  Algebra.TensorProduct.coordinateAlgebra_tower A B D I.associatedGraded
local instance : Algebra.IsPushout B D (B ⊗[A] I.associatedGraded) (D ⊗[A] I.associatedGraded) :=
  Algebra.TensorProduct.coordinateAlgebra_isPushout A B D I.associatedGraded

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [mB : Module B M] [mC : Module (B ⊗[A] I.associatedGraded) M]
  [hC : IsScalarTower B (B ⊗[A] I.associatedGraded) M]
  [mD : Module D N] [mE : Module (D ⊗[A] I.associatedGraded) N]
  [hE : IsScalarTower D (D ⊗[A] I.associatedGraded) N]

/-- Coordinate base change detects bijectivity of the original tensor-algebra extension. -/
theorem associatedGradedCoordinateLiftBaseChange_bijective :
    letI : Module (B ⊗[A] I.associatedGraded) N :=
      Module.compHom (R := D ⊗[A] I.associatedGraded) (S := B ⊗[A] I.associatedGraded) N
        (algebraMap (B ⊗[A] I.associatedGraded) (D ⊗[A] I.associatedGraded))
    letI : IsScalarTower (B ⊗[A] I.associatedGraded) (D ⊗[A] I.associatedGraded) N :=
      IsScalarTower.of_compHom _ _ _
    ∀ (f : M →ₗ[B ⊗[A] I.associatedGraded] N) (e : D ⊗[B] M ≃ₗ[D] N),
      (∀ x, e (1 ⊗ₜ[B] x) = f x) →
        Function.Bijective (f.liftBaseChange (D ⊗[A] I.associatedGraded)) := by
  let : Module (B ⊗[A] I.associatedGraded) N :=
    Module.compHom (R := D ⊗[A] I.associatedGraded) (S := B ⊗[A] I.associatedGraded) N
      (algebraMap (B ⊗[A] I.associatedGraded) (D ⊗[A] I.associatedGraded))
  let : IsScalarTower (B ⊗[A] I.associatedGraded) (D ⊗[A] I.associatedGraded) N :=
    IsScalarTower.of_compHom _ _ _
  intro f e he
  exact Algebra.TensorProduct.coordinateLiftBaseChange_bijective A B D I.associatedGraded
    (mC := mC) (mE := mE) (hC := hC) (hE := hE) f e he

/-- It suffices to check the original coordinate comparison on homogeneous generators. -/
theorem associatedGradedCoordinateLiftBaseChange_bijective_of_directSum
    (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module B (P n)]
    [mCP : Module (B ⊗[A] I.associatedGraded) (⨁ n, P n)]
    [hCP : IsScalarTower B (B ⊗[A] I.associatedGraded) (⨁ n, P n)] :
    letI : Module (B ⊗[A] I.associatedGraded) N :=
      Module.compHom (R := D ⊗[A] I.associatedGraded) (S := B ⊗[A] I.associatedGraded) N
        (algebraMap (B ⊗[A] I.associatedGraded) (D ⊗[A] I.associatedGraded))
    letI : IsScalarTower (B ⊗[A] I.associatedGraded) (D ⊗[A] I.associatedGraded) N :=
      IsScalarTower.of_compHom _ _ _
    ∀ (f : (⨁ n, P n) →ₗ[B ⊗[A] I.associatedGraded] N)
      (e : D ⊗[B] (⨁ n, P n) ≃ₗ[D] N),
      (∀ n x, e (1 ⊗ₜ[B] DirectSum.of P n x) = f (DirectSum.of P n x)) →
        Function.Bijective (f.liftBaseChange (D ⊗[A] I.associatedGraded)) := by
  let : Module (B ⊗[A] I.associatedGraded) N :=
    Module.compHom (R := D ⊗[A] I.associatedGraded) (S := B ⊗[A] I.associatedGraded) N
      (algebraMap (B ⊗[A] I.associatedGraded) (D ⊗[A] I.associatedGraded))
  let : IsScalarTower (B ⊗[A] I.associatedGraded) (D ⊗[A] I.associatedGraded) N :=
    IsScalarTower.of_compHom _ _ _
  intro f e he
  apply I.associatedGradedCoordinateLiftBaseChange_bijective B D
    (mC := mCP) (mE := mE) (hC := hCP) (hE := hE) f e
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | of n x => exact he n x
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

end Ideal
