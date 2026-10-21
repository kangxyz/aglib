/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.IsTensorProduct

/-! # The original tensor-coordinate square is an algebra pushout -/

@[expose] public noncomputable section

open scoped TensorProduct
namespace Algebra.TensorProduct

variable (A B D S : Type*) [CommRing A] [CommRing B] [CommRing D] [CommRing S]
  [Algebra A B] [Algebra A D] [Algebra A S] [Algebra B D] [IsScalarTower A B D]

/-- Scalar extension in the coordinate factor, leaving the other factor unchanged. -/
@[instance_reducible]
def coordinateAlgebra : Algebra (B ⊗[A] S) (D ⊗[A] S) :=
  (map (IsScalarTower.toAlgHom A B D) (AlgHom.id A S)).toRingHom.toAlgebra

/-- Coordinate tensor scalars act through the original coordinate algebra map. -/
local instance instCoordinateTensorAlgebra :
    Algebra (B ⊗[A] S) (D ⊗[A] S) := coordinateAlgebra A B D S

/-- The tensor-coordinate action retains the original coordinate scalar tower. -/
theorem coordinateAlgebra_tower : IsScalarTower B (B ⊗[A] S) (D ⊗[A] S) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext b
  change algebraMap B D b ⊗ₜ[A] (1 : S) =
    map (IsScalarTower.toAlgHom A B D) (AlgHom.id A S) (b ⊗ₜ[A] (1 : S))
  rw [map_tmul]
  rfl

local instance : IsScalarTower B (B ⊗[A] S) (D ⊗[A] S) :=
  coordinateAlgebra_tower A B D S

/-- The actual coordinate tensor map gives the canonical pushout square. -/
theorem coordinateAlgebra_isPushout : Algebra.IsPushout B D (B ⊗[A] S) (D ⊗[A] S) := by
  apply Algebra.IsPushout.tensorProduct_tensorProduct A S B D
  ext s
  change map (IsScalarTower.toAlgHom A B D) (AlgHom.id A S) ((1 : B) ⊗ₜ[A] s) =
    (1 : D) ⊗ₜ[A] s
  simp only [map_tmul, map_one, AlgHom.id_apply]

end Algebra.TensorProduct
