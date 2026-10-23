/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeComparison

/-! # Original square-map sections on an arbitrary scheme cocone -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Functor

/-- Keep a functor's objects and replace its maps by provably identical original maps. -/
def withActualMaps {J C : Type*} [Category J] [Category C]
    (G : J ⥤ C) (r : ∀ {j k}, (j ⟶ k) → (G.obj j ⟶ G.obj k))
    (hr : ∀ {j k} (m : j ⟶ k), r m = G.map m) : J ⥤ C where
  obj := G.obj
  map := r
  map_id j := (hr (𝟙 j)).trans (G.map_id j)
  map_comp m n := (hr (m ≫ n)).trans
    ((G.map_comp m n).trans (by rw [hr m, hr n]))

/-- The original-map presentation is identified by identity components. -/
def withActualMapsIso {J C : Type*} [Category J] [Category C]
    (G : J ⥤ C) (r : ∀ {j k}, (j ⟶ k) → (G.obj j ⟶ G.obj k))
    (hr : ∀ {j k} (m : j ⟶ k), r m = G.map m) : withActualMaps G r hr ≅ G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun m =>
    (Category.comp_id _).trans ((hr m).trans (Category.id_comp _).symm))

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (c : Cocone X)

/-- The original square sections on an arbitrary native scheme cone. -/
def coneOriginalSectionsFunctor : I ⥤ AddCommGrpCat.{u + 1} :=
  Functor.withActualMaps (coneCoefficientFunctor X c F ⋙ globalSections c.pt.unop)
    (fun a => coneSystemSectionsMap X F c a)
    (fun a => coneSystemSectionsMap_eq X F c a)

/-- Identity on objects identifies original square maps with coefficient-section maps. -/
def coneOriginalSectionsIso :
    coneOriginalSectionsFunctor X F c ≅
      coneCoefficientFunctor X c F ⋙ globalSections c.pt.unop :=
  Functor.withActualMapsIso (coneCoefficientFunctor X c F ⋙ globalSections c.pt.unop)
    (fun a => coneSystemSectionsMap X F c a)
    (fun a => coneSystemSectionsMap_eq X F c a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
