/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Functor.ImageCompositionExchange
public import Aglib.CategoryTheory.Functor.CompositionExchangeTransport
public import Aglib.CategoryTheory.NatTrans.CompositeExchangeLiftFormula

/-! # Whole original composition exchange through native property lifts -/
@[expose] public noncomputable section
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


/-- Restrict the whole original model law before specializing any native component.
Every comparison remains the supplied original map. -/
theorem imageCompositionExchange_restrict
    (σ : Q ⋙ I ⟶ L ⋙ R) (σ' : Q' ⋙ I' ⟶ L' ⋙ R')
    (c : K ⋙ L ≅ J) (c' : K' ⋙ L' ≅ J')
    (s : R ⋙ P ≅ S) (s' : R' ⋙ P' ≅ S')
    (βQ : Q ⋙ FM ⟶ FB ⋙ Q') (βP : P ⋙ FZ ⟶ FN ⋙ P')
    (βS : S ⋙ FZ ⟶ FC ⋙ S')
    (eK : K ⋙ FB ≅ FA ⋙ K') (eI : I ⋙ FN ≅ FM ⋙ I')
    (eJ : J ⋙ FC ≅ FA ⋙ J')
    (PA : ObjectProperty A) (PM : ObjectProperty M) (PZ : ObjectProperty Z)
    (PA' : ObjectProperty A') (PM' : ObjectProperty M') (PZ' : ObjectProperty Z')
    (hF : ∀ X : PA.FullSubcategory, PM ((PA.ι ⋙ (K ⋙ Q)).obj X))
    (hG : ∀ X : PM.FullSubcategory, PZ ((PM.ι ⋙ (I ⋙ P)).obj X))
    (hH : ∀ X : PA.FullSubcategory, PZ ((PA.ι ⋙ (J ⋙ S)).obj X))
    (hF' : ∀ X : PA'.FullSubcategory, PM' ((PA'.ι ⋙ (K' ⋙ Q')).obj X))
    (hG' : ∀ X : PM'.FullSubcategory, PZ' ((PM'.ι ⋙ (I' ⋙ P')).obj X))
    (hH' : ∀ X : PA'.FullSubcategory, PZ' ((PA'.ι ⋙ (J' ⋙ S')).obj X))
    (hA : ∀ X : PA.FullSubcategory, PA' ((PA.ι ⋙ FA).obj X))
    (hM : ∀ X : PM.FullSubcategory, PM' ((PM.ι ⋙ FM).obj X))
    (hZ : ∀ X : PZ.FullSubcategory, PZ' ((PZ.ι ⋙ FZ).obj X))
    (κ : PM.lift (PA.ι ⋙ (K ⋙ Q)) hF ⋙ PZ.lift (PM.ι ⋙ (I ⋙ P)) hG ≅
      PZ.lift (PA.ι ⋙ (J ⋙ S)) hH)
    (κ' : PM'.lift (PA'.ι ⋙ (K' ⋙ Q')) hF' ⋙ PZ'.lift (PM'.ι ⋙ (I' ⋙ P')) hG' ≅
      PZ'.lift (PA'.ι ⋙ (J' ⋙ S')) hH')
    (α : (PA.ι ⋙ K) ⋙ Q ⋙ I ⋙ P ⟶ (PA.ι ⋙ J) ⋙ S)
    (α' : (PA'.ι ⋙ K') ⋙ Q' ⋙ I' ⋙ P' ⟶ (PA'.ι ⋙ J') ⋙ S')
    (hκ : Functor.whiskerRight κ.hom PZ.ι = α)
    (hκ' : Functor.whiskerRight κ'.hom PZ'.ι = α')
    (hα : ImageCompositionFormula σ (Functor.isoWhiskerLeft PA.ι c) s α)
    (hα' : ImageCompositionFormula σ' (Functor.isoWhiskerLeft PA'.ι c') s' α')
    (γF : (PA.ι ⋙ (K ⋙ Q)) ⋙ FM ⟶ PA'.lift (PA.ι ⋙ FA) hA ⋙ (PA'.ι ⋙ (K' ⋙ Q')))
    (γG : (PM.ι ⋙ (I ⋙ P)) ⋙ FZ ⟶ PM'.lift (PM.ι ⋙ FM) hM ⋙ (PM'.ι ⋙ (I' ⋙ P')))
    (γH : (PA.ι ⋙ (J ⋙ S)) ⋙ FZ ⟶ PA'.lift (PA.ι ⋙ FA) hA ⋙ (PA'.ι ⋙ (J' ⋙ S')))
    (hγF : CompositeExchangeLiftFormula PA PA' FA (K ⋙ Q) (K' ⋙ Q') FM hA
      (compositeExchange βQ eK) γF)
    (hγG : CompositeExchangeLiftFormula PM PM' FM (I ⋙ P) (I' ⋙ P') FZ hM
      (compositeExchange βP eI) γG)
    (hγH : CompositeExchangeLiftFormula PA PA' FA (J ⋙ S) (J' ⋙ S') FZ hA
      (compositeExchange βS eJ) γH)
    (δF : PM.lift (PA.ι ⋙ (K ⋙ Q)) hF ⋙ PM'.lift (PM.ι ⋙ FM) hM ⟶
      PA'.lift (PA.ι ⋙ FA) hA ⋙ PM'.lift (PA'.ι ⋙ (K' ⋙ Q')) hF')
    (δG : PZ.lift (PM.ι ⋙ (I ⋙ P)) hG ⋙ PZ'.lift (PZ.ι ⋙ FZ) hZ ⟶
      PM'.lift (PM.ι ⋙ FM) hM ⋙ PZ'.lift (PM'.ι ⋙ (I' ⋙ P')) hG')
    (δH : PZ.lift (PA.ι ⋙ (J ⋙ S)) hH ⋙ PZ'.lift (PZ.ι ⋙ FZ) hZ ⟶
      PA'.lift (PA.ι ⋙ FA) hA ⋙ PZ'.lift (PA'.ι ⋙ (J' ⋙ S')) hH')
    (hδF : Functor.whiskerRight δF PM'.ι = γF)
    (hδG : Functor.whiskerRight δG PZ'.ι = γG)
    (hδH : Functor.whiskerRight δH PZ'.ι = γH)
    (h : ImageCompositionExchangeEquation (imageCompositionMap σ c s)
      (imageCompositionMap σ' c' s') βQ βP βS eK eI eJ) :
    CompositionExchangeEquation κ κ' δF δG δH := by
  intro X
  apply ObjectProperty.hom_ext
  have hk := congrArg (fun t => t.app X) hκ
  have hk' := congrArg (fun t => t.app ((PA'.lift (PA.ι ⋙ FA) hA).obj X)) hκ'
  have hdF := congrArg (fun t => t.app X) hδF
  have hdG := congrArg (fun t => t.app ((PM.lift (PA.ι ⋙ (K ⋙ Q)) hF).obj X)) hδG
  have hdH := congrArg (fun t => t.app X) hδH
  simp only [Functor.whiskerRight_app, ObjectProperty.ι_map] at hk hk' hdF hdG hdH
  change FZ.map ((κ.hom.app X).hom) ≫ (δH.app X).hom =
    (δG.app ((PM.lift (PA.ι ⋙ (K ⋙ Q)) hF).obj X)).hom ≫
      (I' ⋙ P').map ((δF.app X).hom) ≫
        (κ'.hom.app ((PA'.lift (PA.ι ⋙ FA) hA).obj X)).hom
  rw [hk, hk', hdF, hdG, hdH, hγF, hγG, hγH, hα, hα']
  have hh := h X.obj
  simpa only [imageCompositionMap, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, compositeExchange_app, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, Functor.isoWhiskerLeft_hom, ObjectProperty.lift,
    ObjectProperty.ι_obj, Category.assoc] using hh

end CategoryTheory
