/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.ScalarForgetting

/-! # Whole comparison aliases in scalar-forgetting coherence

The original composition, square, exchange and endpoint-comparison aliases
remain parameters. Their defining equations are normalized before concrete
sites or coefficients are substituted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory

section Composition

variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
  {L₀ : A ⥤ C} {R₀ : C ⥤ A} {L₀' : D ⥤ F} {R₀' : F ⥤ D}

/-- Actual comparison aliases give the normalized original left composition square. -/
theorem scalarComparison_comp
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (adj₀ : L₀ ⊣ R₀) (adj₀' : L₀' ⊣ R₀')
    (e₁ : L₁ ⋙ H ≅ G ⋙ L₂) (e₂ : L₃ ⋙ K ≅ H ⋙ L₄)
    (e₀ : L₀ ⋙ K ≅ G ⋙ L₀')
    (r₁ : R₁ ⋙ G ≅ H ⋙ R₂) (r₂ : R₃ ⋙ H ≅ K ⋙ R₄)
    (r₀ : R₀ ⋙ G ≅ K ⋙ R₀')
    (c₁ : L₀ ≅ L₁ ⋙ L₃) (c₂ : L₀' ≅ L₂ ⋙ L₄)
    (d₁ : R₀ ≅ R₃ ⋙ R₁) (d₂ : R₀' ≅ R₄ ⋙ R₂)
    (he₁ : mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e₁.inv) =
      TwoSquare.mk _ _ _ _ r₁.hom)
    (he₂ : mateEquiv adj₃ adj₄ (TwoSquare.mk _ _ _ _ e₂.inv) =
      TwoSquare.mk _ _ _ _ r₂.hom)
    (he₀ : mateEquiv adj₀ adj₀' (TwoSquare.mk _ _ _ _ e₀.inv) =
      TwoSquare.mk _ _ _ _ r₀.hom)
    (hc₁ : conjugateEquiv (adj₁.comp adj₃) adj₀ c₁.hom = d₁.inv)
    (hc₂ : conjugateEquiv (adj₂.comp adj₄) adj₀' c₂.hom = d₂.inv)
    (hr : ∀ M, G.map (d₁.hom.app M) ≫ r₁.hom.app (R₃.obj M) ≫
      R₂.map (r₂.hom.app M) = r₀.hom.app M ≫ d₂.hom.app (K.obj M)) (X : A) :
    c₂.hom.app (G.obj X) ≫ L₄.map (e₁.inv.app X) ≫ e₂.inv.app (L₁.obj X) =
      e₀.inv.app X ≫ K.map (c₁.hom.app X) := by
  exact verticalSquareEquation_of_mateEquation
    (TwoSquare.mk _ _ _ _ e₁.inv) (TwoSquare.mk _ _ _ _ e₂.inv)
    (TwoSquare.mk _ _ _ _ e₀.inv) c₁ c₂ d₁ d₂
    adj₁ adj₂ adj₃ adj₄ adj₀ adj₀' hc₁ hc₂ (fun M => by
      dsimp only [VerticalMateEquation]
      rw [he₁, he₂, he₀]
      exact hr M) X

end Composition

section Square

variable {C D : Type*} [Category* C] [Category* D] (U : C ⥤ D)
  {A₀ A₁ B₀ B₁ : C} {C₀ C₁ D₀ D₁ : D}

/-- Retain the original square isomorphisms while normalizing their defining chains. -/
theorem scalarComparison_square
    (a : A₀ ≅ A₁) (b : B₀ ≅ B₁) (q : A₀ ≅ B₀)
    (a' : C₀ ≅ C₁) (b' : D₀ ≅ D₁) (q' : C₀ ≅ D₀)
    (p : A₁ ≅ B₁) (p' : C₁ ≅ D₁)
    (hp : p = a.symm ≪≫ q ≪≫ b) (hp' : p' = a'.symm ≪≫ q' ≪≫ b')
    (s : C₁ ⟶ U.obj A₁) (t : D₁ ⟶ U.obj B₁)
    (v : C₀ ⟶ U.obj A₀) (w : D₀ ⟶ U.obj B₀)
    (ha : a'.hom ≫ s = v ≫ U.map a.hom)
    (hb : b'.hom ≫ t = w ≫ U.map b.hom)
    (hq : q'.hom ≫ w = v ≫ U.map q.hom) :
    s ≫ U.map p.hom = p'.hom ≫ t := by
  subst p
  subst p'
  exact comparison_square_of_comp U a b q a' b' q' s t v w ha hb hq

end Square

section Cube

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : C' ⥤ D'} {R₂' : D' ⥤ C'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}

/-- The native source comparison for a scalar-forgotten original exchange. -/
def scalarMateSourceIso (r₁ : R₁ ⋙ QA ≅ QB ⋙ R₁') (eG : G ⋙ QC ≅ QA ⋙ G') :
    (R₁ ⋙ G) ⋙ QC ≅ QB ⋙ (R₁' ⋙ G') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R₁ eG ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight r₁ G' ≪≫
      Functor.associator _ _ _

/-- The native target comparison for a scalar-forgotten original exchange. -/
def scalarMateTargetIso (r₂ : R₂ ⋙ QC ≅ QD ⋙ R₂') (eH : H ⋙ QD ≅ QB ⋙ H') :
    (H ⋙ R₂) ⋙ QC ≅ QB ⋙ (H' ⋙ R₂') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft H r₂ ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eH R₂' ≪≫
      Functor.associator _ _ _

/-- Normalize the full coefficient cube at the original mate and comparison aliases. -/
theorem scalarComparison_mate
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (e₁ : L₁ ⋙ QB ≅ QA ⋙ L₁') (e₂ : L₂ ⋙ QD ≅ QC ⋙ L₂')
    (r₁ : R₁ ⋙ QA ≅ QB ⋙ R₁') (r₂ : R₂ ⋙ QC ≅ QD ⋙ R₂')
    (eG : G ⋙ QC ≅ QA ⋙ G') (eH : H ⋙ QD ≅ QB ⋙ H')
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (β' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (hβ : β = (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).natTrans)
    (hβ' : β' = (mateEquiv adj₁' adj₂' (TwoSquare.mk _ _ _ _ α')).natTrans)
    (s : (R₁ ⋙ G) ⋙ QC ≅ QB ⋙ (R₁' ⋙ G'))
    (t : (H ⋙ R₂) ⋙ QC ≅ QB ⋙ (H' ⋙ R₂'))
    (hs : s = scalarMateSourceIso r₁ eG) (ht : t = scalarMateTargetIso r₂ eH)
    (he₁ : mateEquiv adj₁ adj₁' (TwoSquare.mk _ _ _ _ e₁.inv) =
      TwoSquare.mk _ _ _ _ r₁.hom)
    (he₂ : mateEquiv adj₂ adj₂' (TwoSquare.mk _ _ _ _ e₂.inv) =
      TwoSquare.mk _ _ _ _ r₂.hom)
    (h : ∀ X, (L₂'.map (eG.inv.app X) ≫ e₂.inv.app (G.obj X)) ≫ QD.map (α.app X) =
      α'.app (QA.obj X) ≫ (H'.map (e₁.inv.app X) ≫ eH.inv.app (L₁.obj X))) (K : B) :
    QC.map (β.app K) ≫ t.hom.app K = s.hom.app K ≫ β'.app (QB.obj K) := by
  subst s
  subst t
  subst β
  subst β'
  have hc := mateEquiv_horizontal_cube adj₁ adj₂ adj₁' adj₂'
    (TwoSquare.mk _ _ _ _ e₁.inv) (TwoSquare.mk _ _ _ _ e₂.inv)
    (TwoSquare.mk _ _ _ _ α) (TwoSquare.mk _ _ _ _ α') eG.inv eH.inv
    (fun X => by simpa only [TwoSquare.hComp_app, Category.assoc] using h X) K
  rw [he₁, he₂] at hc
  have he := hom_square_of_inv (eG.app (R₁.obj K)) (R₂'.mapIso (eH.app K))
    (QC.map ((mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).natTrans.app K) ≫
      r₂.hom.app (H.obj K))
    (G'.map (r₁.hom.app K) ≫
      (mateEquiv adj₁' adj₂' (TwoSquare.mk _ _ _ _ α')).natTrans.app (QB.obj K))
    (by simpa only [TwoSquare.mk, TwoSquare.natTrans, Functor.comp_obj,
      Functor.mapIso_inv, Iso.app_inv, Category.assoc] using hc)
  simpa only [scalarMateSourceIso, scalarMateTargetIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_id,
    Functor.mapIso_hom, Iso.app_hom, Category.id_comp, Category.comp_id,
    Category.assoc] using he

end Cube

end CategoryTheory
