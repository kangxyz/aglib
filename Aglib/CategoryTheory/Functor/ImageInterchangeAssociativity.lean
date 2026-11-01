/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.NaturalPastedRectangle

/-! # Associativity of the original image interchange

The two routes are forced by horizontal and vertical pasting of the specified
original exchanges, and naturality of the middle exchange. No associativity
of the desired final image construction is a premise.
-/

@[expose] public section
namespace CategoryTheory

variable {A₀ A₁ A₂ B₀ B₁ Y Z C : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂] [Category* B₀] [Category* B₁]
  [Category* Y] [Category* Z] [Category* C]
  {Q₀ : A₀ ⥤ Y} {I₁ : Y ⥤ B₀} {M₀₁ : A₀ ⥤ A₁} {R₀₁ : A₁ ⥤ B₀}
  {Q₁ : B₀ ⥤ Z} {I₂ : Z ⥤ C} {M₁₂ : B₀ ⥤ B₁} {R₁₂ : B₁ ⥤ C}
  {N : A₁ ⥤ A₂} {R₀₂ : A₂ ⥤ B₁}
  {Vsrc : A₁ ⥤ Z} {Vtgt : A₂ ⥤ C} {Hsrc : Y ⥤ B₁} {Htgt : A₀ ⥤ A₂}
  (σa : Q₀ ⋙ I₁ ⟶ M₀₁ ⋙ R₀₁)
  (σb : Q₁ ⋙ I₂ ⟶ M₁₂ ⋙ R₁₂)
  (σc : R₀₁ ⋙ M₁₂ ⟶ N ⋙ R₀₂)
  (σv : Vsrc ⋙ I₂ ⟶ N ⋙ Vtgt) (σh : Q₀ ⋙ Hsrc ⟶ Htgt ⋙ R₀₂)
  (dv : Vsrc ≅ R₀₁ ⋙ Q₁) (ev : Vtgt ≅ R₀₂ ⋙ R₁₂)
  (dh : Hsrc ≅ I₁ ⋙ M₁₂) (eh : Htgt ≅ M₀₁ ⋙ N)

/-- The original horizontal route is kept whole before native specialization. -/
def ImageHorizontalInterchange : Prop :=
  ∀ K, ActualHorizontalMateEquation σa σc σh dh.hom eh.hom K

/-- The two original three-step routes, with all specified compositors retained. -/
def ImageInterchangeAssociativityEquation : Prop :=
  ∀ K,
    I₂.map (Q₁.map (σa.app K)) ≫ I₂.map (dv.inv.app (M₀₁.obj K)) ≫
        σv.app (M₀₁.obj K) ≫ ev.hom.app (N.obj (M₀₁.obj K)) =
      σb.app (I₁.obj (Q₀.obj K)) ≫ R₁₂.map (dh.inv.app (Q₀.obj K)) ≫
        R₁₂.map (σh.app K) ≫ R₁₂.map (R₀₂.map (eh.hom.app K))

/-- Actual horizontal/vertical pasting and exchange naturality force associativity. -/
theorem imageInterchangeAssociativityEquation
    (hv : ActualVerticalMatePasting σb σc σv dv.hom ev.hom)
    (hh : ImageHorizontalInterchange σa σc σh dh eh) :
    ImageInterchangeAssociativityEquation σa σb σv σh dv ev dh eh := by
  intro K
  have hvK := hv (M₀₁.obj K)
  have hhK := hh K
  change I₂.map (dv.hom.app (M₀₁.obj K)) ≫ σb.app (R₀₁.obj (M₀₁.obj K)) ≫
      R₁₂.map (σc.app (M₀₁.obj K)) =
    σv.app (M₀₁.obj K) ≫ ev.hom.app (N.obj (M₀₁.obj K)) at hvK
  change dh.hom.app (Q₀.obj K) ≫ M₁₂.map (σa.app K) ≫ σc.app (M₀₁.obj K) =
    σh.app K ≫ R₀₂.map (eh.hom.app K) at hhK
  have hvN : I₂.map (dv.inv.app (M₀₁.obj K)) ≫ σv.app (M₀₁.obj K) ≫
      ev.hom.app (N.obj (M₀₁.obj K)) =
      σb.app (R₀₁.obj (M₀₁.obj K)) ≫ R₁₂.map (σc.app (M₀₁.obj K)) := by
    rw [← hvK]
    simp only [← Category.assoc, ← I₂.map_comp, Iso.inv_hom_id_app,
      I₂.map_id, Category.id_comp]
  have hhN : dh.inv.app (Q₀.obj K) ≫ σh.app K ≫ R₀₂.map (eh.hom.app K) =
      M₁₂.map (σa.app K) ≫ σc.app (M₀₁.obj K) := by
    rw [← hhK]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [hvN]
  have hr := congrArg (fun t => R₁₂.map t) hhN
  simp only [Functor.map_comp] at hr
  rw [hr]
  have hn := σb.naturality (σa.app K)
  change I₂.map (Q₁.map (σa.app K)) ≫ σb.app (R₀₁.obj (M₀₁.obj K)) =
    σb.app (I₁.obj (Q₀.obj K)) ≫ R₁₂.map (M₁₂.map (σa.app K)) at hn
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ R₁₂.map (σc.app (M₀₁.obj K))) hn

end CategoryTheory
