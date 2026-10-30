/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.Terminal
public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.SourceCoherence

/-! # Original constant-source composition from actual adjunction mates

The actual right-adjoint comparison and its section compatibility construct
the left composition comparison. The ordinary source composition and inverse
composition equations follow from the same original mate construction. The
four actual categories retain independent object and morphism universes.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe uC vC uD vD uE vE uV vV

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] {V : Type uV} [Category.{vV} V]
  {K₀ : V ⥤ C} {Γ₀ : C ⥤ V} {K₁ : V ⥤ D} {Γ₁ : D ⥤ V}
  {K₂ : V ⥤ E} {Γ₂ : E ⥤ V}
  {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ E} {S : E ⥤ D}
  {H : C ⥤ E} {T : E ⥤ C}
  (constantAdj₀ : K₀ ⊣ Γ₀) (constantAdj₁ : K₁ ⊣ Γ₁) (constantAdj₂ : K₂ ⊣ Γ₂)
  (imageAdj₁ : F ⊣ R) (imageAdj₂ : G ⊣ S) (imageAdj₀ : H ⊣ T)
  (e₁ : R ⋙ Γ₀ ≅ Γ₁) (e₂ : S ⋙ Γ₁ ≅ Γ₂) (e₀ : T ⋙ Γ₀ ≅ Γ₂)
  (r : S ⋙ R ≅ T)
  (hr : Functor.isoWhiskerLeft S e₁ ≪≫ e₂ =
    (Functor.associator S R Γ₀).symm ≪≫ Functor.isoWhiskerRight r Γ₀ ≪≫ e₀)
  (c₁ : K₀ ⋙ F ≅ K₁) (c₂ : K₁ ⋙ G ≅ K₂) (c₀ : K₀ ⋙ H ≅ K₂)
  (hc₁ : c₁ = leftAdjointCompIso constantAdj₀ imageAdj₁ constantAdj₁ e₁)
  (hc₂ : c₂ = leftAdjointCompIso constantAdj₁ imageAdj₂ constantAdj₂ e₂)
  (hc₀ : c₀ = leftAdjointCompIso constantAdj₀ imageAdj₀ constantAdj₂ e₀)
  (i : H ≅ F ⋙ G) (hi : i = (leftAdjointCompIso imageAdj₁ imageAdj₂ imageAdj₀ r).symm)

include hc₁ hc₂ hc₀ hi hr in
/-- The original constant source maps compose through the actual left comparison. -/
theorem originalSource_comp (A : V) :
    i.hom.app (K₀.obj A) ≫ G.map (c₁.hom.app A) ≫ c₂.hom.app A = c₀.hom.app A := by
  subst c₁
  subst c₂
  subst c₀
  subst i
  have h := leftAdjointCompIso_assoc
    constantAdj₀ imageAdj₁ imageAdj₂ constantAdj₁ imageAdj₀ constantAdj₂
    e₁ r e₀ e₂ hr
  have hA := congrArg (fun e => e.hom.app A) h
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at hA
  change (leftAdjointCompIso imageAdj₁ imageAdj₂ imageAdj₀ r).hom.app (K₀.obj A) ≫
      (leftAdjointCompIso constantAdj₀ imageAdj₀ constantAdj₂ e₀).hom.app A =
    G.map ((leftAdjointCompIso constantAdj₀ imageAdj₁ constantAdj₁ e₁).hom.app A) ≫
      (leftAdjointCompIso constantAdj₁ imageAdj₂ constantAdj₂ e₂).hom.app A at hA
  rw [← hA]
  simp

include hc₁ hc₂ hc₀ hi hr in
/-- The corresponding original inverse-source equation, with the same comparisons. -/
theorem originalSource_comp_inv (A : V) :
    c₀.inv.app A ≫ i.hom.app (K₀.obj A) = c₂.inv.app A ≫ G.map (c₁.inv.app A) := by
  apply (cancel_mono (G.map (c₁.hom.app A) ≫ c₂.hom.app A)).mp
  simp only [Category.assoc]
  rw [originalSource_comp constantAdj₀ constantAdj₁ constantAdj₂
    imageAdj₁ imageAdj₂ imageAdj₀ e₁ e₂ e₀ r hr c₁ c₂ c₀ hc₁ hc₂ hc₀ i hi]
  simp [← Functor.map_comp_assoc]

end CategoryTheory.Adjunction
