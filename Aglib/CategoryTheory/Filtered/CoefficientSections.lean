/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.Cone

/-! # One actual coefficient-section diagram and its original cocone

The existing coefficient functor is followed by the supplied actual section
functor. The cocone is its image of the SAME chosen coefficient-colimit cocone.
No section preservation, filteredness, geometry or alternative functor is input.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem.AdjunctionData.Cone

universe uI vI uA vA uB vB uV vV

variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)]
  {D : InjectiveSystem.AdjunctionData A}
  {B : Type uB} [Category.{vB} B] (P : D.Cone B)
  (F : InjectiveSystem.System D)
  {V : Type uV} [Category.{vV} V] (Γ : B ⥤ V)

/-- Sections of the original coefficient diagram, at arbitrary independent index size. -/
def coefficientSectionsFunctor : I ⥤ V := P.coefficientFunctor F ⋙ Γ

/-- The whole map is the section image of the original coefficient map. -/
theorem coefficientSectionsFunctor_map {i j : I} (a : i ⟶ j) :
    (P.coefficientSectionsFunctor F Γ).map a = Γ.map (P.coefficientMap F a) := rfl

/-- The original mapped coefficient-colimit cocone. -/
def coefficientSectionsCocone [HasColimit (P.coefficientFunctor F)] :
    Cocone (P.coefficientSectionsFunctor F Γ) :=
  Γ.mapCocone (colimit.cocone (P.coefficientFunctor F))

/-- Each section leg is the image of the same original coefficient insertion. -/
@[reassoc]
theorem coefficientSectionsCocone_ι [HasColimit (P.coefficientFunctor F)] (i : I) :
    (P.coefficientSectionsCocone F Γ).ι.app i =
      Γ.map (colimit.ι (P.coefficientFunctor F) i) := rfl

end CategoryTheory.InjectiveSystem.AdjunctionData.Cone
