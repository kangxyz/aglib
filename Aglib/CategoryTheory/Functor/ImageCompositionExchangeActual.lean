/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionExchange
public import Aglib.CategoryTheory.Functor.CompositionExchangeTransport
public import Aglib.CategoryTheory.NatTrans.CompositeExchange

/-! # The whole image exchange law for the actual supplied compositors -/
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


/-- The actual compositor formulas turn the proved original model law into the
same composition-exchange equation, without replacing any map. -/
theorem imageCompositionExchange_actual
    (σ : Q ⋙ I ⟶ L ⋙ R) (σ' : Q' ⋙ I' ⟶ L' ⋙ R')
    (c : K ⋙ L ≅ J) (c' : K' ⋙ L' ≅ J')
    (s : R ⋙ P ≅ S) (s' : R' ⋙ P' ≅ S')
    (βQ : Q ⋙ FM ⟶ FB ⋙ Q') (βP : P ⋙ FZ ⟶ FN ⋙ P')
    (βS : S ⋙ FZ ⟶ FC ⋙ S')
    (eK : K ⋙ FB ≅ FA ⋙ K') (eI : I ⋙ FN ≅ FM ⋙ I')
    (eJ : J ⋙ FC ≅ FA ⋙ J')
    (κ : (K ⋙ Q) ⋙ (I ⋙ P) ≅ J ⋙ S)
    (κ' : (K' ⋙ Q') ⋙ (I' ⋙ P') ≅ J' ⋙ S')
    (hκ : ImageCompositionFormula σ c s κ.hom)
    (hκ' : ImageCompositionFormula σ' c' s' κ'.hom)
    (h : ImageCompositionExchangeEquation (imageCompositionMap σ c s)
      (imageCompositionMap σ' c' s') βQ βP βS eK eI eJ) :
    CompositionExchangeEquation κ κ' (compositeExchange βQ eK)
      (compositeExchange βP eI) (compositeExchange βS eJ) := by
  rw [imageCompositionMap_eq σ c s κ.hom hκ,
    imageCompositionMap_eq σ' c' s' κ'.hom hκ'] at h
  intro X
  simpa only [compositeExchange_app, Functor.comp_map, Functor.map_comp,
    Functor.comp_obj, Category.assoc] using h X

end CategoryTheory
