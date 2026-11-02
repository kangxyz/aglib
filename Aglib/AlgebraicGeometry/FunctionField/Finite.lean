/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.GenericFiber

/-! # Finite maps on the actual function fields

The general finite-dominant theorem is extracted, unchanged, from
`Curves/Isogeny/Etale.lean`; curve-specific consumers import this lower leaf.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual generic-field map of a finite dominant morphism is finite. -/
theorem functionFieldMap_finite (f : X ⟶ Y) [IsDominant f] [IsFinite f] :
    (functionFieldMap f).Finite := by
  let : IsIso (genericFibreMap f) := genericFibreMap_isIso f
  have h : IsFinite (Spec.map (CommRingCat.ofHom (functionFieldMap f))) := by
    rw [← show genericFibreMap f ≫ pullback.snd f (Y.fromSpecStalk (genericPoint Y)) =
      Spec.map (CommRingCat.ofHom (functionFieldMap f)) from pullback.lift_snd _ _ _]
    infer_instance
  exact (IsFinite.SpecMap_iff _).mp h

end AlgebraicGeometry.Scheme
