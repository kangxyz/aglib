/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.MixedMateNormalization
public import Aglib.CategoryTheory.Adjunction.UnitRestriction

/-! # Whole natural-transformation normalization of a restricted mixed mate -/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

variable {A B C D T : Type*} [Category A] [Category B] [Category C] [Category D]
  [Category T] {J : A ⥤ B} {Q : B ⥤ A} {J' : C ⥤ D} {Q' : D ⥤ C}
  {P : B ⥤ D} {R : D ⥤ B} {P' : A ⥤ C} {R' : C ⥤ A}
  (aJ : J ⊣ Q) (aJ' : J' ⊣ Q') (aP : P ⊣ R) (aP' : P' ⊣ R')
  (α : J ⋙ P ⟶ P' ⋙ J') (β : R ⋙ Q ≅ Q' ⋙ R')
  (h : conjugateEquiv (aP'.comp aJ') (aJ.comp aP) α = β.inv)
  (I : T ⥤ C) [IsIso aJ'.unit]
  (γ : R ⋙ Q ⟶ Q' ⋙ R') (hγ : β.hom = γ)
  (ρ : (I ⋙ J' ⋙ R) ⋙ Q ⟶ I ⋙ R') [IsIso ρ]
  (hρ : ρ = Functor.restrictionOfUnit I J' Q' R Q R' γ (asIso aJ'.unit))

include h hγ hρ

/-- The original adjoint of inverse restriction equals the original mixed mate,
as an equality of whole natural transformations before specializing categories. -/
theorem restrictionComparison_eq_mate :
    Functor.whiskerRight (asIso ρ).inv J ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (I ⋙ J' ⋙ R) aJ.counit ≫
      (Functor.rightUnitor _).hom =
    (Functor.associator I R' J).hom ≫
      Functor.whiskerLeft I (mateEquiv aP' aP (TwoSquare.mk _ _ _ _ α)).natTrans := by
  apply NatTrans.ext
  funext K
  apply (aJ.homEquiv _ _).injective
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id]
  rw [← aJ.homEquiv_symm_apply, Equiv.apply_symm_apply]
  apply (cancel_mono (ρ.app K)).mp
  have hi := (asIso ρ).inv_hom_id_app K
  simp only [asIso_hom] at hi
  rw [hi]
  have hn := mixedMate_homEquiv_restriction aJ aJ' aP aP' α β h (I.obj K)
  rw [hγ] at hn
  rw [hρ, Functor.restrictionOfUnit_app]
  simp only [asIso_inv, NatIso.isIso_inv_app]
  convert hn.symm using 1 <;>
    simp [mateEquiv]

end CategoryTheory.Adjunction
