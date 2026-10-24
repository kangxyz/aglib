/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.SquareZero.ClosedImmersion
public import Aglib.AlgebraicGeometry.Properties.AffineLocalSections

/-!
# Square-zero ring kernels on every open

For a quasi-compact morphism `i` with intrinsic square-zero kernel `i.ker ^ 2 = ⊥`, the ring
kernel of `i.app V` is square-zero on every open `V`, not only on affine opens
(`AlgebraicGeometry.Scheme.Modules.Invertible.ker_app_sq_eq_bot`). Restrictions of kernel
sections to affine opens stay in the kernel, where `ker_app_sq_of_kernel_sq` applies, and
sections vanishing on every affine open vanish.

The current consumer is the split thickening unit sequence
(`Aglib.AlgebraicGeometry.Picard.Tangent.Thickening`).
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- The intrinsic square-zero kernel gives square-zero ring kernels on every open, not
only on affine opens. -/
theorem ker_app_sq_eq_bot {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [QuasiCompact i]
    (hi : i.ker ^ 2 = ⊥) (V : X.Opens) : RingHom.ker (i.app V).hom ^ 2 = ⊥ := by
  rw [pow_two]
  apply le_antisymm _ bot_le
  apply Ideal.mul_le.mpr
  intro x hx y hy
  apply Ideal.mem_bot.mpr
  apply eq_zero_of_forall_affine (x * y)
  intro W hW hWV
  have hres : ∀ z ∈ RingHom.ker (i.app V).hom,
      (X.presheaf.map (homOfLE hWV).op).hom z ∈ RingHom.ker (i.app W).hom := by
    intro z hz
    rw [RingHom.mem_ker] at hz ⊢
    have e := congrArg (fun φ => φ.hom z) (i.naturality (homOfLE hWV).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    rw [e, hz, map_zero]
  rw [map_mul]
  exact Ideal.mul_eq_zero_of_mem_of_square_zero _ (ker_app_sq_of_kernel_sq i hi ⟨W, hW⟩)
    (hres x hx) (hres y hy)

end AlgebraicGeometry.Scheme.Modules.Invertible
