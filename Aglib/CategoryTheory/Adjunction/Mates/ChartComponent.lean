/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.Mates.Chart

/-! # Original component transport with one fixed category dictionary -/
@[expose] public section
namespace CategoryTheory.SourceChartMates
variable {C : Type*} [Category C] {X Y Z W : C}

/-- Only the original middle morphism needs an invertibility proof. -/
theorem component_isIso (s : X ≅ Y) (a : Y ⟶ Z) (t : Z ≅ W)
    (h : IsIso a) : IsIso (s.hom ≫ a ≫ t.hom) := by
  let : IsIso a := h
  infer_instance

/-- The exact same original word is epi. -/
theorem component_epi (s : X ≅ Y) (a : Y ⟶ Z) (t : Z ≅ W)
    (h : IsIso a) : Epi (s.hom ≫ a ≫ t.hom) := by
  let : IsIso a := h
  infer_instance

end CategoryTheory.SourceChartMates
