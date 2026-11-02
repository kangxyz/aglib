/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Sheafification comparison from an original restricted presheaf

The complete comparison and its forward-arrow formula use the native
restriction/sheafification compatibility and the original sheafification unit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace CategoryTheory.Functor

universe v v' w' u u' w

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) (A : Type w) [Category.{w'} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  (F : Sheaf J A) (P : Dᵒᵖ ⥤ A) (H : Sheaf K A)
  (E : F.obj ≅ G.op ⋙ P) (O : (presheafToSheaf K A).obj P ≅ H)

/-- An original restricted-presheaf isomorphism and an original sheafification
comparison assemble to a sheaf isomorphism without a new sheaf model. -/
def restrictedSheafificationComparison :
    F ≅ (G.sheafPushforwardContinuous A J K).obj H :=
  ObjectProperty.isoMk _ (isoSheafify J F.property) ≪≫
    (presheafToSheaf J A).mapIso E ≪≫
    (G.pushforwardContinuousSheafificationCompatibility A J K).app P ≪≫
    (G.sheafPushforwardContinuous A J K).mapIso O

/-- The whole forward arrow is the original presheaf comparison followed by
the restriction of the original sheafification unit and final comparison. -/
theorem restrictedSheafificationComparison_hom :
    (G.restrictedSheafificationComparison A J K F P H E O).hom.hom =
      E.hom ≫ whiskerLeft G.op (toSheafify K P ≫ O.hom.hom) := by
  let T := (G.pushforwardContinuousSheafificationCompatibility A J K).app P
  have hn := (sheafificationAdjunction J A).unit.naturality E.hom
  change E.hom ≫ toSheafify J (G.op ⋙ P) =
    toSheafify J F.obj ≫ ((presheafToSheaf J A).map E.hom).hom at hn
  have ht := G.toSheafify_pullbackSheafificationCompatibility A J K P
  change toSheafify J F.obj ≫ ((presheafToSheaf J A).map E.hom).hom ≫
    T.hom.hom ≫ whiskerLeft G.op O.hom.hom = _
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]
  rw [← Category.assoc (toSheafify J (G.op ⋙ P))]
  dsimp only [T]
  erw [ht]
  rw [whiskerLeft_comp]

end CategoryTheory.Functor
