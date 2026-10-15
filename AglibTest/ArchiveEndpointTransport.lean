/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Triangulated.EndpointTransport

/-! The transported triangle retains all three actual arrows and specified endpoint maps. -/
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
universe u v u' v'

namespace AglibTest.ArchiveEndpointTransport

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C] [HasShift C ℤ]
  (A : J ⥤ Triangle C) {F₁ F₂ F₃ : J ⥤ C}
  (e₁ : F₁ ≅ A ⋙ Triangle.π₁) (e₂ : F₂ ≅ A ⋙ Triangle.π₂)
  (e₃ : F₃ ≅ A ⋙ Triangle.π₃)

/-- The first transported arrow is conjugated by the two specified endpoint isomorphisms. -/
theorem first_arrow (j : J) :
    ((Triangle.transportEndpoints A e₁ e₂ e₃).obj j).mor₁ =
      e₁.hom.app j ≫ (A.obj j).mor₁ ≫ e₂.inv.app j := rfl

/-- The second transported arrow uses the original middle and third endpoint maps. -/
theorem second_arrow (j : J) :
    ((Triangle.transportEndpoints A e₁ e₂ e₃).obj j).mor₂ =
      e₂.hom.app j ≫ (A.obj j).mor₂ ≫ e₃.inv.app j := rfl

/-- The last arrow retains the original shift applied to the first inverse endpoint map. -/
theorem third_arrow (j : J) :
    ((Triangle.transportEndpoints A e₁ e₂ e₃).obj j).mor₃ =
      e₃.hom.app j ≫ (A.obj j).mor₃ ≫
        (shiftFunctor C (1 : ℤ)).map (e₁.inv.app j) := rfl

/-- The displayed comparison has exactly the original three endpoint components. -/
theorem comparison_components (j : J) :
    ((Triangle.transportEndpointsIso A e₁ e₂ e₃).hom.app j).hom₁ = e₁.hom.app j ∧
      ((Triangle.transportEndpointsIso A e₁ e₂ e₃).hom.app j).hom₂ = e₂.hom.app j ∧
        ((Triangle.transportEndpointsIso A e₁ e₂ e₃).hom.app j).hom₃ = e₃.hom.app j :=
  ⟨rfl, rfl, rfl⟩

end AglibTest.ArchiveEndpointTransport
