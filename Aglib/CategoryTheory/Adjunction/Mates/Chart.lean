/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.Mates.InverseNaturality

/-! # Whole source-chart comparison and its native mate

All categories, original functors, adjunctions and boundary isomorphisms are
parameters. The original words of maps are retained; the geometric instances
need no normalization inside a sheafification model.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory.SourceChartMates
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀}
  {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
  {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
  {P : C₀ ⥤ C₁} {Q : D₀ ⥤ D₁}
  {F : C₁ ⥤ C₂} {G : D₁ ⥤ D₂}
  {A : C₀ ⥤ C₂} {B : D₀ ⥤ D₂}

/-- The original source boundary and associator. -/
def sourceIso (s : A ≅ P ⋙ F) (L₂ : C₂ ⥤ D₂) :
    A ⋙ L₂ ≅ P ⋙ (F ⋙ L₂) :=
  isoWhiskerRight s L₂ ≪≫ associator P F L₂

/-- The original inverse-image square and target boundary. -/
def targetIso (e : P ⋙ L₁ ≅ L₀ ⋙ Q) (t : B ≅ Q ⋙ G) :
    P ⋙ (L₁ ⋙ G) ≅ L₀ ⋙ B :=
  (associator P L₁ G).symm ≪≫ isoWhiskerRight e G ≪≫
    associator L₀ Q G ≪≫ isoWhiskerLeft L₀ t.symm

/-- The unchanged source-chart word of ordinary comparison maps. -/
def comparison (e : P ⋙ L₁ ≅ L₀ ⋙ Q) (α : F ⋙ L₂ ⟶ L₁ ⋙ G)
    (s : A ≅ P ⋙ F) (t : B ≅ Q ⋙ G) : A ⋙ L₂ ⟶ L₀ ⋙ B :=
  (sourceIso s L₂).hom ≫ whiskerLeft P α ≫ (targetIso e t).hom

/-- The actual word is the boundary-normalized original horizontal pasting. -/
theorem comparison_eq_hcomp (e : P ⋙ L₁ ≅ L₀ ⋙ Q) (α : F ⋙ L₂ ⟶ L₁ ⋙ G)
    (s : A ≅ P ⋙ F) (t : B ≅ Q ⋙ G) :
    comparison e α s t = whiskerRight s.hom L₂ ≫
      (TwoSquare.hComp (TwoSquare.mk _ _ _ _ e.hom) (TwoSquare.mk _ _ _ _ α)).natTrans ≫
        whiskerLeft L₀ t.inv := by
  apply NatTrans.ext
  funext X
  simp [comparison, sourceIso, targetIso, TwoSquare.hComp, TwoSquare.natTrans,
    Category.assoc]

/-- Invertibility requires only the actual middle component. -/
theorem comparison_isIso (e : P ⋙ L₁ ≅ L₀ ⋙ Q) (α : F ⋙ L₂ ⟶ L₁ ⋙ G)
    (s : A ≅ P ⋙ F) (t : B ≅ Q ⋙ G) (X : C₀)
    (h : IsIso (α.app (P.obj X))) : IsIso ((comparison e α s t).app X) := by
  let : IsIso (α.app (P.obj X)) := h
  dsimp only [comparison, NatTrans.comp_app, whiskerLeft_app]
  infer_instance

/-- The original right-adjoint word, using the two actual comparison isomorphisms. -/
def rightIso (δ₁ : R₀ ⋙ P ≅ Q ⋙ R₁) (δ₂ : R₁ ⋙ F ≅ G ⋙ R₂)
    (s : A ≅ P ⋙ F) (t : B ≅ Q ⋙ G) : R₀ ⋙ A ≅ B ⋙ R₂ :=
  isoWhiskerLeft R₀ s ≪≫ (associator R₀ P F).symm ≪≫
    isoWhiskerRight δ₁ F ≪≫ associator Q R₁ F ≪≫ isoWhiskerLeft Q δ₂ ≪≫
    (associator Q G R₂).symm ≪≫ isoWhiskerRight t.symm R₂

/-- Whole original mate computation, independent of all geometric models. -/
theorem mate_comparison (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (e : P ⋙ L₁ ≅ L₀ ⋙ Q) (α : F ⋙ L₂ ⟶ L₁ ⋙ G)
    (s : A ≅ P ⋙ F) (t : B ≅ Q ⋙ G)
    (δ₁ : R₀ ⋙ P ≅ Q ⋙ R₁) (δ₂ : R₁ ⋙ F ≅ G ⋙ R₂)
    (h₁ : (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ e.hom)).natTrans = δ₁.hom)
    (h₂ : (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ α)).natTrans = δ₂.hom) :
    (mateEquiv a₀ a₂ (TwoSquare.mk _ _ _ _ (comparison e α s t))).natTrans =
      (rightIso δ₁ δ₂ s t).hom := by
  apply NatTrans.ext
  funext K
  rw [comparison_eq_hcomp]
  refine (mateEquiv_boundary_iso_app a₀ a₂
    (TwoSquare.hComp (TwoSquare.mk _ _ _ _ e.hom) (TwoSquare.mk _ _ _ _ α))
    s t.symm K).trans ?_
  rw [mateEquiv_hComp_app a₀ a₁ a₂]
  have h₁' := congrArg (fun z => z.app K) h₁
  have h₂' := congrArg (fun z => z.app (Q.obj K)) h₂
  change (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ e.hom)).app K = δ₁.hom.app K at h₁'
  change (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ α)).app (Q.obj K) =
    δ₂.hom.app (Q.obj K) at h₂'
  rw [h₁', h₂']
  simp [rightIso, Category.assoc]

end CategoryTheory.SourceChartMates
