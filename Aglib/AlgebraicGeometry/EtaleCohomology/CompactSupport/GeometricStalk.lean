/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleStalkInside
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldSections

/-! # Actual module geometric stalks and field sections

The existing native module stalk and its inverse-image comparison are reused.
The comparison with sections is their original adjunction mate followed by the
original field terminal germ, with the same constant-ring coefficient model.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (Λ : Type (u + 1)) [CommRing Λ]

/-- A geometric stalk is actual module sections of the original geometric pullback. -/
def moduleGeometricStalkSectionsIso (s : Spec (.of Ω) ⟶ X) :
    moduleGeometricStalk Λ s ≅
      moduleInverseImage s Λ ⋙ moduleGlobalSections (Spec (.of Ω)) Λ := by
  have e := moduleStalkInverseImageIso s (𝟙 (Spec (.of Ω))) Λ
  simp only [Category.id_comp] at e
  exact e ≪≫ Functor.isoWhiskerLeft (moduleInverseImage s Λ)
    (moduleFieldSectionsFiberIso Ω Λ).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
