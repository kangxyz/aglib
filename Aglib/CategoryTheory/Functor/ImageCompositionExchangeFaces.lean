/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionExchange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SquarePasting

/-! # Original compositor exchange in contraction orientation -/

@[expose] public section

namespace CategoryTheory

section Open
variable {A B C A' B' C' : Type*}
  [Category* A] [Category* B] [Category* C]
  [Category* A'] [Category* B'] [Category* C']
  {K : A ⥤ B} {J : A ⥤ C} {L : B ⥤ C}
  {K' : A' ⥤ B'} {J' : A' ⥤ C'} {L' : B' ⥤ C'}
  {FA : A ⥤ A'} {FB : B ⥤ B'} {FC : C ⥤ C'}

/-- Original horizontal square pasting gives the contraction-oriented open face. -/
theorem imageCompositionOpenExchange_of_horizontal
    (c : J ≅ K ⋙ L) (c' : J' ≅ K' ⋙ L')
    (eK : K ⋙ FB ≅ FA ⋙ K') (eJ : J ⋙ FC ≅ FA ⋙ J')
    (eL : L ⋙ FC ≅ FB ⋙ L')
    (h : ∀ X, HorizontalSquareEquation
      (TwoSquare.mk _ _ _ _ eK.hom) (TwoSquare.mk _ _ _ _ eL.hom)
      (TwoSquare.mk _ _ _ _ eJ.hom) c.hom c'.hom X) :
    ImageCompositionOpenExchange c.symm c'.symm eK eJ eL := by
  intro X
  have hh := congrArg (fun z => FC.map (c.inv.app X) ≫ z ≫ c'.inv.app (FA.obj X)) (h X)
  dsimp only [HorizontalSquareEquation, TwoSquare.mk, TwoSquare.natTrans] at hh
  simp only [Category.assoc, ← FC.map_comp_assoc, Iso.inv_hom_id_app,
    FC.map_id, Category.id_comp, Iso.hom_inv_id_app] at hh
  simpa only [Functor.comp_obj, Category.comp_id, Iso.symm_hom] using hh.symm

end Open

section Proper
variable {C N Z C' N' Z' : Type*}
  [Category* C] [Category* N] [Category* Z]
  [Category* C'] [Category* N'] [Category* Z']
  {R : C ⥤ N} {P : N ⥤ Z} {S : C ⥤ Z}
  {R' : C' ⥤ N'} {P' : N' ⥤ Z'} {S' : C' ⥤ Z'}
  {FC : C ⥤ C'} {FN : N ⥤ N'} {FZ : Z ⥤ Z'}

/-- Original proper-compositor exchange gives its contraction-oriented face. -/
theorem imageCompositionProperExchange_of_pasting
    (s : S ≅ R ⋙ P) (s' : S' ≅ R' ⋙ P')
    (βR : R ⋙ FN ⟶ FC ⋙ R') (βP : P ⋙ FZ ⟶ FN ⋙ P')
    (βS : S ⋙ FZ ⟶ FC ⋙ S')
    (h : ∀ X, FZ.map (s.hom.app X) ≫ βP.app (R.obj X) ≫ P'.map (βR.app X) =
      βS.app X ≫ s'.hom.app (FC.obj X)) :
    ImageCompositionProperExchange s.symm s'.symm βR βP βS := by
  intro X
  have hh := congrArg
    (fun z => FZ.map (s.inv.app X) ≫ z ≫ s'.inv.app (FC.obj X)) (h X)
  simp only [Category.assoc, ← FZ.map_comp_assoc, Iso.inv_hom_id_app,
    FZ.map_id, Category.id_comp, Iso.hom_inv_id_app] at hh
  simpa only [Functor.comp_obj, Category.comp_id, Iso.symm_hom] using hh.symm

end Proper

end CategoryTheory
