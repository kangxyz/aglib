/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap

/-! # Whole natural-transformation comparison for the original inverse-image square -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

/-- Normalize the entire comparison before evaluating any concrete component. -/
theorem iso_comparison_square {C : Type*} [Category* C] {A B D E : C}
    (e₁ : A ≅ B) (t : A ≅ D) (e₂ : D ≅ E) :
    e₁.hom ≫ (e₁.symm ≪≫ t ≪≫ e₂).hom = t.hom ≫ e₂.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

end CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- Whole-functor comparison retains the actual square and native composition isomorphisms. -/
theorem inverseImageSquareIso_comp_hom {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    (inverseImageComp g f').hom ≫ (inverseImageSquareIso f f' g g' h).hom =
      eqToHom (congrArg (fun t : X' ⟶ S => inverseImage t) h) ≫
        (inverseImageComp f g').hom :=
  iso_comparison_square (inverseImageComp g f')
    (eqToIso (congrArg (fun t : X' ⟶ S => inverseImage t) h)) (inverseImageComp f g')

end AlgebraicGeometry.Scheme.EtaleCohomology
