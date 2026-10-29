/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Topos.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Ordinary points from the native fibre and skyscraper adjunction

For a chosen topos category, a point has inverse image to the selected category
of sets. The point package is only a transparent specialization of the actual
left-exact adjunction; it does not assert that an arbitrary category is a topos.
A native site point supplies this data on the original Set-valued sheaves.
Its geometric interpretation retains the proved size conditions of the chosen
sheaf topos. No enough-points hypothesis or new stalk realization is introduced.

The unit-coordinate law below is a computation in a site presentation. Its
arbitrary coefficient category is a coefficient action, not a claim that all
coefficient-valued sheaf categories are topoi.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

universe w v u v' u'

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]

/-- In a site presentation, the actual skyscraper unit evaluates to the original germ. -/
@[reassoc]
theorem skyscraperSheafAdjunction_unit_π (L : Sheaf J A) (U : C) (p : Φ.fiber.obj U) :
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

end CategoryTheory.GrothendieckTopology.Point

namespace CategoryTheory.Topos

/-- Point data on a chosen category, geometrically a morphism from sets when
that parent category is a topos. No topos-existence assertion is part of this alias. -/
abbrev Point (E : Type u') [Category.{v'} E] :=
  GeometricMorphism (Type w) E

namespace Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [LocallySmall.{w} C] (Φ : GrothendieckTopology.Point.{w} J)

/-- The native site point, with exactly its original fibre, skyscraper and adjunction. -/
def ofSitePoint : Point (Sheaf J (Type w)) :=
  LeftExactAdjunction.ofAdjunction (Φ.skyscraperSheafAdjunction (A := Type w))

@[simp]
theorem ofSitePoint_inverseImage :
    (ofSitePoint Φ).left.obj = Φ.sheafFiber (A := Type w) := rfl

@[simp]
theorem ofSitePoint_directImage :
    (ofSitePoint Φ).right = Φ.skyscraperSheafFunctor (A := Type w) := rfl

@[simp]
theorem ofSitePoint_adjunction :
    (ofSitePoint Φ).adj = Φ.skyscraperSheafAdjunction (A := Type w) := rfl

/-- The actual Set-point unit recovers the original section germ in this presentation. -/
@[reassoc]
theorem ofSitePoint_unit_π (L : Sheaf J (Type w)) (U : C) (p : Φ.fiber.obj U) :
    ((ofSitePoint Φ).adj.unit.app L).hom.app (op U) ≫
        Pi.π (fun _ : Φ.fiber.obj U => Φ.sheafFiber.obj L) p =
      Φ.toPresheafFiber U p L.obj :=
  Φ.skyscraperSheafAdjunction_unit_π L U p

end Point
end CategoryTheory.Topos
