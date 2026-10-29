/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits

/-! # Colimit preservation detected by a jointly conservative family

A functor preserves colimits of a given shape if this holds after composition
with each functor in a jointly conservative family that preserves those colimits.
The target of the original functor is assumed to have colimits of that shape.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits

universe vA vB vD vJ uA uB uD uI uJ

/-- A jointly conservative family that preserves colimits detects preservation
of colimits of the same shape by the original functor. -/
theorem preservesColimitsOfShape_of_jointlyReflectIsomorphisms
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    {I : Type uI} {D : I → Type uD} [∀ i, Category.{vD} (D i)]
    {J : Type uJ} [Category.{vJ} J]
    (H : A ⥤ B) (P : ∀ i, B ⥤ D i) (hP : JointlyReflectIsomorphisms P)
    [HasColimitsOfShape J B]
    [∀ i, PreservesColimitsOfShape J (P i)]
    [∀ i, PreservesColimitsOfShape J (H ⋙ P i)] :
    PreservesColimitsOfShape J H where
  preservesColimit {_K} := {
    preserves := fun {_c} hc => ⟨hP.jointlyReflectsColimit
      (fun i => isColimitOfPreserves (H ⋙ P i) hc)⟩ }

end CategoryTheory.Limits
