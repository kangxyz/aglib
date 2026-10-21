/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.Basic

/-! # The algebra-hom universal property of Néron modifications -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Algebra.NeronModification

variable {B C ι : Type*} [CommRing B] [CommRing C] [Algebra B C]
variable (p : B) (g : ι → B) (z : ι → C)
variable (hz : ∀ i, algebraMap B C p * z i = algebraMap B C (g i))
variable (hp : IsRegular (algebraMap B C p))

/-- Divisibility witnesses in a regular target define an actual algebra homomorphism. -/
def liftAlgHom : Modification p g →ₐ[B] C where
  toRingHom := lift p g (algebraMap B C) z hz hp
  commutes' b := by
    change lift p g (algebraMap B C) z hz hp (of p g b) = algebraMap B C b
    exact lift_of p g (algebraMap B C) z hz hp b

/-- The algebra lift preserves the original coefficients. -/
@[simp] theorem liftAlgHom_of (b : B) :
    liftAlgHom p g z hz hp (of p g b) = algebraMap B C b :=
  lift_of p g (algebraMap B C) z hz hp b

/-- The algebra lift takes each divided coordinate to its specified witness. -/
@[simp] theorem liftAlgHom_coordinate (i : ι) :
    liftAlgHom p g z hz hp (coordinate p g i) = z i :=
  lift_coordinate p g (algebraMap B C) z hz hp i

include hp in
/-- Regularity of the distinguished element makes algebra maps from the modification unique. -/
theorem algHom_ext_of_isRegular (φ ψ : Modification p g →ₐ[B] C) : φ = ψ := by
  let w := fun i => φ (coordinate p g i)
  have hw (i : ι) : algebraMap B C p * w i = algebraMap B C (g i) := by
    rw [← φ.commutes p, ← φ.commutes (g i)]
    change φ (of p g p) * φ (coordinate p g i) = φ (of p g (g i))
    rw [← map_mul, of_mul_coordinate]
  apply AlgHom.coe_ringHom_injective
  apply (lift_unique p g (algebraMap B C) w hw hp φ.toRingHom ?_).trans
    (lift_unique p g (algebraMap B C) w hw hp ψ.toRingHom ?_).symm
  · ext b
    exact φ.commutes b
  · ext b
    exact ψ.commutes b

end Algebra.NeronModification
