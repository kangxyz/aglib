/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.KrullDimension.FlatLocal
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Properties

/-! # Original codimension under a flat scheme morphism -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The image of an original point under a flat morphism has no larger codimension.
This is the actual stalk-map dimension inequality, without finiteness hypotheses. -/
theorem coheight_image_le_of_flat {X Y : Scheme} (f : X ⟶ Y) [Flat f] (x : X) :
    Order.coheight (f x) ≤ Order.coheight x := by
  have h := RingHom.ringKrullDim_le_of_flat_local (f.stalkMap x).hom (Flat.stalkMap f x)
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact WithBot.coe_le_coe.mp h

end AlgebraicGeometry.Scheme.Hom
