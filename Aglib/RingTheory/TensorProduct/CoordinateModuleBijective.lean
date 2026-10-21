/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.TensorProduct.CoordinatePushout
public import Aglib.RingTheory.TensorProduct.PushoutModuleBijective

/-! # The original scalar-extension map in a tensor-coordinate square -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable (A B D S : Type*) [CommRing A] [CommRing B] [CommRing D] [CommRing S]
  [Algebra A B] [Algebra A D] [Algebra A S] [Algebra B D] [IsScalarTower A B D]

/-- The base-change comparison uses the original coordinate tensor algebra action. -/
local instance instCoordinateBaseChangeAlgebra :
    Algebra (B ⊗[A] S) (D ⊗[A] S) := coordinateAlgebra A B D S
local instance : IsScalarTower B (B ⊗[A] S) (D ⊗[A] S) :=
  coordinateAlgebra_tower A B D S
local instance : Algebra.IsPushout B D (B ⊗[A] S) (D ⊗[A] S) :=
  coordinateAlgebra_isPushout A B D S

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [mB : Module B M] [mC : Module (B ⊗[A] S) M]
  [hC : IsScalarTower B (B ⊗[A] S) M]
  [mD : Module D N] [mE : Module (D ⊗[A] S) N]
  [hE : IsScalarTower D (D ⊗[A] S) N]

/-- Coordinate base change detects bijectivity of the original tensor-algebra extension. -/
theorem coordinateLiftBaseChange_bijective :
    letI : Module (B ⊗[A] S) N :=
      Module.compHom (R := D ⊗[A] S) (S := B ⊗[A] S) N
        (algebraMap (B ⊗[A] S) (D ⊗[A] S))
    letI : IsScalarTower (B ⊗[A] S) (D ⊗[A] S) N :=
      IsScalarTower.of_compHom _ _ _
    ∀ (f : M →ₗ[B ⊗[A] S] N) (e : D ⊗[B] M ≃ₗ[D] N),
      (∀ x, e (1 ⊗ₜ[B] x) = f x) → Function.Bijective (f.liftBaseChange (D ⊗[A] S)) := by
  let : Module (B ⊗[A] S) N :=
    Module.compHom (R := D ⊗[A] S) (S := B ⊗[A] S) N
      (algebraMap (B ⊗[A] S) (D ⊗[A] S))
  let : IsScalarTower (B ⊗[A] S) (D ⊗[A] S) N :=
    IsScalarTower.of_compHom _ _ _
  intro f e he
  exact Algebra.IsPushout.liftBaseChange_bijective_of_coordinateEquiv B D
    (B ⊗[A] S) (D ⊗[A] S) f e he

end Algebra.TensorProduct
