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
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (c : Cocone X)

/-- The original square sections on an arbitrary native scheme cone. -/
def coneOriginalSectionsFunctor : I ⥤ AddCommGrpCat.{u + 1} :=
  coneCoefficientSectionsFunctor X c F

/-- The selected single operation retains every whole original square-section map. -/
theorem coneOriginalSectionsFunctor_map {i j : I} (a : i ⟶ j) :
    (coneOriginalSectionsFunctor X F c).map a = coneSystemSectionsMap X F c a :=
  (coneSystemSectionsMap_eq X F c a).symm

/-- Compatibility name only: both sides are now the SAME selected operation. -/
def coneOriginalSectionsIso :
    coneOriginalSectionsFunctor X F c ≅
      coneCoefficientFunctor X c F ⋙ globalSections c.pt.unop := Iso.refl _

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
