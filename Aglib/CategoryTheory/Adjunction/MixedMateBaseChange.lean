/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HorizontalCube

/-! # Base change of original mixed mates

Only the horizontal comparisons are invertible. In particular the right-adjoint
exchange maps need not be invertible. Whole input and output predicates keep
native derived functors opaque when the lemma is specialized.
-/

@[expose] public section

namespace CategoryTheory

open TwoSquare

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : C' ⥤ D'} {R₂' : D' ⥤ C'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}

/-- The original left-adjoint cube, before taking any mates. -/
def MixedMateLeftCube
    (s₁ : QA ⋙ L₁' ⟶ L₁ ⋙ QB) (s₂ : QC ⋙ L₂' ⟶ L₂ ⋙ QD)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (eG : G ⋙ QC ≅ QA ⋙ G') (eH : H ⋙ QD ≅ QB ⋙ H') : Prop :=
  ∀ X, L₂'.map (eG.inv.app X) ≫ s₂.app (G.obj X) ≫ QD.map (α.app X) =
    α'.app (QA.obj X) ≫ H'.map (s₁.app X) ≫ eH.inv.app (L₁.obj X)

/-- The base-change cube for the original right-adjoint mixed mates. -/
def MixedMateBaseChangeEquation
    (r₁ : R₁ ⋙ QA ⟶ QB ⋙ R₁') (r₂ : R₂ ⋙ QC ⟶ QD ⋙ R₂')
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (β' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (eG : G ⋙ QC ≅ QA ⋙ G') (eH : H ⋙ QD ≅ QB ⋙ H') : Prop :=
  ∀ K, QC.map (β.app K) ≫ r₂.app (H.obj K) ≫ R₂'.map (eH.hom.app K) =
    eG.hom.app (R₁.obj K) ≫ G'.map (r₁.app K) ≫ β'.app (QB.obj K)

/-- Taking the original mates of a proved left cube gives their original
base-change equation, without an isomorphism assumption on either exchange. -/
theorem mixedMateBaseChange_of_leftCube
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (s₁ : QA ⋙ L₁' ⟶ L₁ ⋙ QB) (s₂ : QC ⋙ L₂' ⟶ L₂ ⋙ QD)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (eG : G ⋙ QC ≅ QA ⋙ G') (eH : H ⋙ QD ≅ QB ⋙ H')
    (r₁ : R₁ ⋙ QA ⟶ QB ⋙ R₁') (r₂ : R₂ ⋙ QC ⟶ QD ⋙ R₂')
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (β' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (hr₁ : (mateEquiv adj₁ adj₁' (TwoSquare.mk _ _ _ _ s₁)).natTrans = r₁)
    (hr₂ : (mateEquiv adj₂ adj₂' (TwoSquare.mk _ _ _ _ s₂)).natTrans = r₂)
    (hβ : (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).natTrans = β)
    (hβ' : (mateEquiv adj₁' adj₂' (TwoSquare.mk _ _ _ _ α')).natTrans = β')
    (h : MixedMateLeftCube s₁ s₂ α α' eG eH) :
    MixedMateBaseChangeEquation r₁ r₂ β β' eG eH := by
  intro K
  have hc := mateEquiv_horizontal_cube adj₁ adj₂ adj₁' adj₂'
    (TwoSquare.mk _ _ _ _ s₁) (TwoSquare.mk _ _ _ _ s₂)
    (TwoSquare.mk _ _ _ _ α) (TwoSquare.mk _ _ _ _ α') eG.inv eH.inv
    (fun X => by simpa only [TwoSquare.hComp_app, Category.assoc] using h X) K
  change G'.map ((mateEquiv adj₁ adj₁' (TwoSquare.mk _ _ _ _ s₁)).natTrans.app K) ≫
      (mateEquiv adj₁' adj₂' (TwoSquare.mk _ _ _ _ α')).natTrans.app (QB.obj K) ≫
        R₂'.map (eH.inv.app K) =
    eG.inv.app (R₁.obj K) ≫
      QC.map ((mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).natTrans.app K) ≫
        (mateEquiv adj₂ adj₂' (TwoSquare.mk _ _ _ _ s₂)).natTrans.app (H.obj K) at hc
  rw [hr₁, hr₂, hβ, hβ'] at hc
  have hn := congrArg
    (fun t => eG.hom.app (R₁.obj K) ≫ t ≫ R₂'.map (eH.hom.app K)) hc
  simp only [Category.assoc, ← R₂'.map_comp, Iso.inv_hom_id_app,
    Iso.hom_inv_id_app_assoc] at hn
  rw [R₂'.map_id ((QB ⋙ H').obj K)] at hn
  simpa only [Functor.comp_obj, Category.comp_id] using hn.symm

end CategoryTheory
