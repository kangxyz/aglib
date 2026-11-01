/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.Mates

/-! # Actual adjunction maps in a pulled-back localization sequence -/
@[expose] public noncomputable section
namespace CategoryTheory

/-- The original conjugacy of both composite adjunctions identifies the original inverse mate. -/
theorem inverseComparison_mate_of_conjugacy
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {J : A ⥤ B} {RJ : B ⥤ A} {I : C ⥤ D} {RI : D ⥤ C}
    {G : A ⥤ C} {RG : C ⥤ A} {H : B ⥤ D} {RH : D ⥤ B}
    (aj : J ⊣ RJ) (ai : I ⊣ RI) (ag : G ⊣ RG) (ah : H ⊣ RH)
    (e : J ⋙ H ≅ G ⋙ I) (E : RH ⋙ RJ ≅ RI ⋙ RG)
    (α : TwoSquare RJ H G RI)
    (he : conjugateEquiv (ag.comp ai) (aj.comp ah) e.hom = E.inv)
    (hE : E.hom = (mateEquiv ah ag α).natTrans) :
    mateEquiv aj ai (TwoSquare.mk _ _ _ _ e.inv) = α := by
  apply (mateEquiv ah ag).injective
  apply TwoSquare.ext
  rw [iterated_mateEquiv_conjugateEquiv]
  have hi : conjugateIsoEquiv (ag.comp ai) (aj.comp ah) e = E.symm := Iso.ext he
  have hh := congrArg Iso.inv hi
  change conjugateEquiv (aj.comp ah) (ag.comp ai) e.inv = E.hom at hh
  rw [hE] at hh
  intro K
  exact congrArg (fun t => t.app K) hh

/-- The actual first-vertex comparison preserves the original counit. -/
theorem localizationPullback_counit
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {J : A ⥤ B} {U : B ⥤ A} {J' : C ⥤ D} {U' : D ⥤ C}
    {F : B ⥤ D} {G : A ⥤ C} (a : J ⊣ U) (a' : J' ⊣ U')
    (e : J ⋙ F ≅ G ⋙ J') (u : U ⋙ G ≅ F ⋙ U')
    (he : mateEquiv a a' (TwoSquare.mk _ _ _ _ e.inv) = TwoSquare.mk _ _ _ _ u.hom)
    (M : B) :
    (e.hom.app (U.obj M) ≫ J'.map (u.hom.app M)) ≫ a'.counit.app (F.obj M) =
      F.map (a.counit.app M) := by
  have h := mateEquiv_counit a a' (TwoSquare.mk _ _ _ _ e.inv) M
  rw [he] at h
  have h' := congrArg (fun z => e.hom.app (U.obj M) ≫ z) h
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using h'

/-- The actual third-vertex comparison preserves the original unit. -/
theorem localizationPullback_unit
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {U : A ⥤ B} {R : B ⥤ A} {U' : C ⥤ D} {R' : D ⥤ C}
    {F : A ⥤ C} {G : B ⥤ D} (a : U ⊣ R) (a' : U' ⊣ R')
    (u : U ⋙ G ≅ F ⋙ U') (β : R ⋙ F ⟶ G ⋙ R')
    (hβ : (mateEquiv a a' (TwoSquare.mk _ _ _ _ u.inv)).natTrans = β)
    (M : A) :
    F.map (a.unit.app M) ≫ (β.app (U.obj M) ≫ R'.map (u.hom.app M)) =
      a'.unit.app (F.obj M) := by
  have h := unit_mateEquiv a a' (TwoSquare.mk _ _ _ _ u.inv) M
  have h' := congrArg (fun z => z ≫ R'.map (u.hom.app M)) h
  change (F.map (a.unit.app M) ≫
    (mateEquiv a a' (TwoSquare.mk _ _ _ _ u.inv)).natTrans.app (U.obj M)) ≫ _ = _ at h'
  rw [hβ] at h'
  simpa only [TwoSquare.mk, Category.assoc, ← R'.map_comp, Iso.inv_hom_id_app,
    R'.map_id, Functor.comp_obj, Functor.id_obj, Category.comp_id] using h'
end CategoryTheory
