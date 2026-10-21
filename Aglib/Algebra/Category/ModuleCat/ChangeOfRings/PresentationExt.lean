/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Scalar-extension extensionality through an original presentation -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable {B R S : Type u} [CommRing B] [CommRing R] [CommRing S]
  (b : B →+* R) (φ : R →+* S)
  {L : ModuleCat.{max u v} B} {M : ModuleCat.{max u v} R} {N : ModuleCat.{max u v} S}

/-- After identifying the original source with a scalar extension, maps out of
its further scalar extension are determined on the double unit tensors. -/
theorem extendScalars_hom_ext_of_presentation
    (e : M ≅ (extendScalars b).obj L)
    {α β : (extendScalars φ).obj M ⟶ N}
    (h : ∀ m : L, α ((1 : S) ⊗ₜ[R,φ] e.inv ((1 : R) ⊗ₜ[B,b] m)) =
      β ((1 : S) ⊗ₜ[R,φ] e.inv ((1 : R) ⊗ₜ[B,b] m))) : α = β := by
  apply ((extendRestrictScalarsAdj φ).homEquiv M N).injective
  apply (cancel_epi e.inv).mp
  apply ExtendScalars.hom_ext (f := b)
  intro m
  simpa only [comp_apply, extendRestrictScalarsAdj_homEquiv_apply] using h m

end ModuleCat
