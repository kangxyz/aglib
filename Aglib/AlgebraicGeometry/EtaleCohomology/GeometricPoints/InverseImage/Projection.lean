/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Typed evaluation of a native skyscraper unit -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.StalkInverseImage

universe w v u v' u'

section Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : GrothendieckTopology.Point.{w} J) {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]

/-- Evaluating the native skyscraper adjunction unit gives the original colimit germ. -/
theorem pointSkyscraperUnit_π (L : Sheaf J A) (U : C) (p : Φ.fiber.obj U) :
    (Φ.skyscraperSheafAdjunction.unit.app L).hom.app (op U) ≫
        Pi.π (fun _ : Φ.fiber.obj U => Φ.sheafFiber.obj L) p =
      Φ.toPresheafFiber U p L.obj := by
  have hu : (Φ.skyscraperSheafAdjunction.unit.app L).hom =
      Φ.skyscraperPresheafHomEquiv (𝟙 (Φ.sheafFiber.obj L)) := by
    exact (congrArg
      (fun q : L ⟶ Φ.skyscraperSheaf (Φ.sheafFiber.obj L) => q.hom)
      (Φ.skyscraperSheafAdjunction.homEquiv_id L).symm).trans
        (Φ.skyscraperSheafAdjunction_homEquiv_apply_hom (𝟙 (Φ.sheafFiber.obj L)))
  have h := congrArg
    (fun q : L.obj ⟶ Φ.skyscraperPresheaf (Φ.sheafFiber.obj L) =>
      q.app (op U) ≫ Pi.π (fun _ : Φ.fiber.obj U => Φ.sheafFiber.obj L) p) hu
  exact h.trans ((Φ.skyscraperPresheafHomEquiv_app_π (𝟙 _) U p).trans
    (Category.comp_id _))

end Point

section Projection

variable {A : Type u} [Category.{v} A] {V₀ V₁ V₂ V₃ V₄ : A}

/-- Evaluate a composite using its fully typed projection and unit-coordinate equations. -/
theorem projection_composite (a : V₀ ⟶ V₁) (b : V₁ ⟶ V₂)
    (c : V₂ ⟶ V₃) (d : V₃ ⟶ V₄) (e : V₂ ⟶ V₄) (g : V₁ ⟶ V₄)
    (hc : c ≫ d = e) (hb : b ≫ e = g) :
    a ≫ b ≫ c ≫ d = a ≫ g := by
  rw [hc, hb]

end Projection

end AlgebraicGeometry.Scheme.EtaleCohomology.StalkInverseImage
