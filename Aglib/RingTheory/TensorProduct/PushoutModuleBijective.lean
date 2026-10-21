/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.TensorProduct.PushoutModuleEquiv

/-! # Bijectivity of the original module scalar-extension map -/

@[expose] public noncomputable section

open scoped TensorProduct
namespace Algebra.IsPushout

variable (R S C D : Type*) [CommRing R] [CommRing S] [CommRing C] [CommRing D]
  [Algebra R S] [Algebra R C] [Algebra R D] [Algebra C D] [Algebra S D]
  [IsScalarTower R C D] [IsScalarTower R S D] [Algebra.IsPushout R S C D]
  {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module C M] [IsScalarTower R C M]
  [Module C N] [Module S N] [Module D N]
  [IsScalarTower C D N] [IsScalarTower S D N]

/-- The original scalar-extension map is bijective when its coordinate base change is. -/
theorem liftBaseChange_bijective_of_coordinateEquiv (f : M →ₗ[C] N)
    (e : S ⊗[R] M ≃ₗ[S] N) (he : ∀ x, e (1 ⊗ₜ[R] x) = f x) :
    Function.Bijective (f.liftBaseChange D) :=
  (moduleEquivOfCoordinateEquiv R S C D f e he).bijective

end Algebra.IsPushout
