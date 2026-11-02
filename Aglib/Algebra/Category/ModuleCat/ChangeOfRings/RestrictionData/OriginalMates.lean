/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.RestrictionData.Linearization

/-! # Identification with an original scalar-restriction map

The original additive map and scalar adjunction unit identify the same tensor
mate before native cohomology specialization. The geometric consumer supplies
its original restriction map, not a substitute tensor comparison.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u w

namespace ModuleCat.TensorRestrictionData

/-- The lower mate is the mate of any original restriction map with the same
underlying additive map. -/
theorem δ_eq_of_restrictionMap {R S : Type u} [CommRing R] [CommRing S]
    {σ : R →+* S} (d : TensorRestrictionData.{u, w} σ)
    (ρ : d.A' ⟶ (restrictScalars σ).obj d.D) (hρ : ∀ x, ρ x = d.r x) :
    d.δ = ((extendRestrictScalarsAdj.{max u w, u, u} σ).homEquiv _ _).symm ρ := by
  apply d.δ_eq_of_unit
  intro x
  have h := congrArg (fun f => f x)
    (((extendRestrictScalarsAdj.{max u w, u, u} σ).homEquiv _ _).apply_symm_apply ρ)
  exact h.trans (hρ x)

end ModuleCat.TensorRestrictionData
