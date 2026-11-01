/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionMap
public import Aglib.CategoryTheory.Adjunction.MixedMateBaseChange

/-! # Exchange for the original image-composition map

The original mixed-mate cube, open compositor square and proper compositor
square imply the composition-exchange square. All maps remain specified; none
is reconstructed from invertibility.
-/

@[expose] public section

namespace CategoryTheory

variable {A B C M N Z A' B' C' M' N' Z' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* M] [Category* N] [Category* Z]
  [Category* A'] [Category* B'] [Category* C'] [Category* M'] [Category* N'] [Category* Z']
  {K : A ⥤ B} {J : A ⥤ C} {L : B ⥤ C}
  {Q : B ⥤ M} {I : M ⥤ N} {R : C ⥤ N} {P : N ⥤ Z} {S : C ⥤ Z}
  {K' : A' ⥤ B'} {J' : A' ⥤ C'} {L' : B' ⥤ C'}
  {Q' : B' ⥤ M'} {I' : M' ⥤ N'} {R' : C' ⥤ N'} {P' : N' ⥤ Z'} {S' : C' ⥤ Z'}
  {FA : A ⥤ A'} {FB : B ⥤ B'} {FC : C ⥤ C'}
  {FM : M ⥤ M'} {FN : N ⥤ N'} {FZ : Z ⥤ Z'}

/-- Whole exchange compatibility of the specified open compositors. -/
def ImageCompositionOpenExchange
    (c : K ⋙ L ≅ J) (c' : K' ⋙ L' ≅ J')
    (eK : K ⋙ FB ≅ FA ⋙ K') (eJ : J ⋙ FC ≅ FA ⋙ J')
    (eL : L ⋙ FC ≅ FB ⋙ L') : Prop :=
  ∀ X, FC.map (c.hom.app X) ≫ eJ.hom.app X =
    eL.hom.app (K.obj X) ≫ L'.map (eK.hom.app X) ≫ c'.hom.app (FA.obj X)

/-- Whole exchange compatibility of the specified proper compositors. -/
def ImageCompositionProperExchange
    (s : R ⋙ P ≅ S) (s' : R' ⋙ P' ≅ S')
    (βR : R ⋙ FN ⟶ FC ⋙ R') (βP : P ⋙ FZ ⟶ FN ⋙ P')
    (βS : S ⋙ FZ ⟶ FC ⋙ S') : Prop :=
  ∀ X, FZ.map (s.hom.app X) ≫ βS.app X =
    βP.app (R.obj X) ≫ P'.map (βR.app X) ≫ s'.hom.app (FC.obj X)

/-- The original component exchange equation for the two image-composition maps. -/
def ImageCompositionExchangeEquation
    (α : K ⋙ Q ⋙ I ⋙ P ⟶ J ⋙ S) (α' : K' ⋙ Q' ⋙ I' ⋙ P' ⟶ J' ⋙ S')
    (βQ : Q ⋙ FM ⟶ FB ⋙ Q') (βP : P ⋙ FZ ⟶ FN ⋙ P')
    (βS : S ⋙ FZ ⟶ FC ⋙ S')
    (eK : K ⋙ FB ≅ FA ⋙ K') (eI : I ⋙ FN ≅ FM ⋙ I')
    (eJ : J ⋙ FC ≅ FA ⋙ J') : Prop :=
  ∀ X, FZ.map (α.app X) ≫ βS.app (J.obj X) ≫ S'.map (eJ.hom.app X) =
    βP.app (I.obj (Q.obj (K.obj X))) ≫ P'.map (eI.hom.app (Q.obj (K.obj X))) ≫
      P'.map (I'.map (βQ.app (K.obj X))) ≫
        P'.map (I'.map (Q'.map (eK.hom.app X))) ≫ α'.app (FA.obj X)

/-- Three proved original faces and the actual component formulas imply the
whole image-composition exchange law. -/
theorem imageCompositionExchangeEquation
    (σ : Q ⋙ I ⟶ L ⋙ R) (σ' : Q' ⋙ I' ⟶ L' ⋙ R')
    (c : K ⋙ L ≅ J) (c' : K' ⋙ L' ≅ J')
    (s : R ⋙ P ≅ S) (s' : R' ⋙ P' ≅ S')
    (βQ : Q ⋙ FM ⟶ FB ⋙ Q') (βR : R ⋙ FN ⟶ FC ⋙ R')
    (βP : P ⋙ FZ ⟶ FN ⋙ P') (βS : S ⋙ FZ ⟶ FC ⋙ S')
    (eK : K ⋙ FB ≅ FA ⋙ K') (eJ : J ⋙ FC ≅ FA ⋙ J')
    (eL : L ⋙ FC ≅ FB ⋙ L') (eI : I ⋙ FN ≅ FM ⋙ I')
    (α : K ⋙ Q ⋙ I ⋙ P ⟶ J ⋙ S) (α' : K' ⋙ Q' ⋙ I' ⋙ P' ⟶ J' ⋙ S')
    (hα : ImageCompositionFormula σ c s α) (hα' : ImageCompositionFormula σ' c' s' α')
    (hσ : MixedMateBaseChangeEquation βQ βR σ σ' eI eL)
    (hc : ImageCompositionOpenExchange c c' eK eJ eL)
    (hs : ImageCompositionProperExchange s s' βR βP βS) :
    ImageCompositionExchangeEquation α α' βQ βP βS eK eI eJ := by
  intro X
  have hnPσ := βP.naturality (σ.app (K.obj X))
  have hnPc := βP.naturality (R.map (c.hom.app X))
  have hnRc := βR.naturality (c.hom.app X)
  have hns := s'.hom.naturality (eJ.hom.app X)
  have hnσ := σ'.naturality (eK.hom.app X)
  change FZ.map (P.map _) ≫ βP.app _ = βP.app _ ≫ P'.map (FN.map _) at hnPσ hnPc
  change FN.map (R.map _) ≫ βR.app _ = βR.app _ ≫ R'.map (FC.map _) at hnRc
  change P'.map (R'.map _) ≫ s'.hom.app _ = s'.hom.app _ ≫ S'.map _ at hns
  change I'.map (Q'.map _) ≫ σ'.app _ = σ'.app _ ≫ R'.map (L'.map _) at hnσ
  dsimp only [Functor.comp_obj] at hnPσ hnPc hnRc hns hnσ
  rw [hα, hα']
  simp only [FZ.map_comp, Category.assoc]
  rw [reassoc_of% (hs (J.obj X)), reassoc_of% hnPc, reassoc_of% hnPσ]
  rw [← hns]
  simp only [← P'.map_comp_assoc]
  rw [reassoc_of% hnRc]
  simp only [← R'.map_comp]
  rw [hc X]
  simp only [R'.map_comp]
  rw [reassoc_of% (hσ (K.obj X))]
  rw [← reassoc_of% hnσ]

end CategoryTheory
