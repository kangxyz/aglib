/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Scalars.Transfer
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.RestrictionSquare
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Square

/-! # The complete original scalar Ext restriction square

All four Ext diagrams and their coefficient actions are constructed together,
before specializing to native sheaves. The original comparison family and index
transports supply the additive square. Its four scalar compatibilities give the
same scalar-adjunction mates, with the original top and bottom correspondences.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped ChangeOfRings

namespace CategoryTheory.Functor

section Transfer

universe u v u' v' i j k l r w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{max r w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{max r w} D]
  {I : Type i} [Category.{j} I] {J : Type k} [Category.{l} J]

/-- Scalar compatibility of the unchanged exact transfer, supplied by the
accepted coefficient-linear diagram construction at every index. -/
theorem extCoefficientTransfer_smul
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : I ⥤ C) (G : J ⥤ D) (P : I ⥤ J) (e : F ⋙ L ≅ P ⋙ G)
    {R S : Type r} [CommRing R] [CommRing S] (σ : R →+* S)
    (A : C) (B : D) (ρ : R →+* End A) (τ : S →+* End B)
    (φ : L.obj A ⟶ B) (hφ : ∀ a : R, L.map (ρ a) ≫ φ = φ ≫ τ (σ a))
    (n : ℕ) (U : Iᵒᵖ) (a : R) (x : Ext.{max r w} (F.obj U.unop) A n) :
    letI := F.extCoefficientModule A ρ n U
    letI := G.extCoefficientModule B τ n (P.op.obj U)
    L.extCoefficientTransfer (e.inv.app U.unop) φ n (a • x) =
      σ a • (show Ext.{max r w} (G.obj (P.op.obj U).unop) B n from
        L.extCoefficientTransfer (e.inv.app U.unop) φ n x) :=
  ((L.extScalarDiagramMap F G P e σ A B ρ τ φ hφ n).app U).hom.map_smul a x

end Transfer

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ i₀ j₀ i₁ j₁ i₂ j₂ i₃ j₃ r w

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀] [HasExt.{max r w} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{max r w} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{max r w} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasExt.{max r w} C₃]
  {I₀ : Type i₀} [Category.{j₀} I₀] {I₁ : Type i₁} [Category.{j₁} I₁]
  {I₂ : Type i₂} [Category.{j₂} I₂] {I₃ : Type i₃} [Category.{j₃} I₃]
  (Lp : C₀ ⥤ C₁) [Lp.Additive] [PreservesFiniteLimits Lp] [PreservesFiniteColimits Lp]
  (La : C₁ ⥤ C₃) [La.Additive] [PreservesFiniteLimits La] [PreservesFiniteColimits La]
  (Lj : C₀ ⥤ C₂) [Lj.Additive] [PreservesFiniteLimits Lj] [PreservesFiniteColimits Lj]
  (Lb : C₂ ⥤ C₃) [Lb.Additive] [PreservesFiniteLimits Lb] [PreservesFiniteColimits Lb]
  (F₀ : I₀ ⥤ C₀) (F₁ : I₁ ⥤ C₁) (F₂ : I₂ ⥤ C₂) (F₃ : I₃ ⥤ C₃)
  (Hp : I₀ ⥤ I₁) (Ha : I₁ ⥤ I₃) (Hj : I₀ ⥤ I₂) (Hb : I₂ ⥤ I₃)
  (ep : F₀ ⋙ Lp ≅ Hp ⋙ F₁) (ea : F₁ ⋙ La ≅ Ha ⋙ F₃)
  (ej : F₀ ⋙ Lj ≅ Hj ⋙ F₂) (eb : F₂ ⋙ Lb ≅ Hb ⋙ F₃)
  {A₀ : C₀} {A₁ : C₁} {A₂ : C₂} {A₃ : C₃}
  (φp : Lp.obj A₀ ⟶ A₁) (φa : La.obj A₁ ⟶ A₃)
  (φj : Lj.obj A₀ ⟶ A₂) (φb : Lb.obj A₂ ⟶ A₃) (n : ℕ)
  {R S : Type r} [CommRing R] [CommRing S] (σ : R →+* S)
  (ρ₀ : R →+* End A₀) (ρ₁ : S →+* End A₁)
  (ρ₂ : R →+* End A₂) (ρ₃ : S →+* End A₃)
  (hp : ∀ a : R, Lp.map (ρ₀ a) ≫ φp = φp ≫ ρ₁ (σ a))
  (ha : ∀ a : S, La.map (ρ₁ a) ≫ φa = φa ≫ ρ₃ a)
  (hj : ∀ a : R, Lj.map (ρ₀ a) ≫ φj = φj ≫ ρ₂ a)
  (hb : ∀ a : R, Lb.map (ρ₂ a) ≫ φb = φb ≫ ρ₃ (σ a))
  (τ : ∀ i : I₀ᵒᵖ, Ha.op.obj (Hp.op.obj i) ⟶ Hb.op.obj (Hj.op.obj i))
  (i : I₀ᵒᵖ) {d : I₂ᵒᵖ} (κJ : Hj.op.obj i ⟶ d)
  (κA : Ha.op.obj (Hp.op.obj i) ⟶ Hb.op.obj d)
  (hk : τ i ≫ Hb.op.map κJ = κA)
  (h : ∀ v,
    ((Lp.extDiagramMap F₀ (Hp ⋙ F₁) ep φp n).app v ≫
      (La.extDiagramMap F₁ (Ha ⋙ F₃) ea φa n).app (Hp.op.obj v)) ≫
        ((F₃.op ⋙ extFunctor.{max r w} n).flip.obj A₃).map (τ v) =
    (Lj.extDiagramMap F₀ (Hj ⋙ F₂) ej φj n).app v ≫
      (Lb.extDiagramMap F₂ (Hb ⋙ F₃) eb φb n).app (Hj.op.obj v))

/-- Construct all original Ext actions, four edges and the scalar square at
once, retaining both actual lower-row index transports. -/
def extScalarRestrictionSquare : Square (ModuleCat.{max r w} S) := by
  let s := Lp.extDiagramRestrictionSquare La Lj Lb F₀ F₁ F₂ F₃ Hp Ha Hj Hb
    ep ea ej eb φp φa φj φb n τ i κJ κA hk h
  letI := F₀.extCoefficientModule A₀ ρ₀ n i
  letI := F₁.extCoefficientModule A₁ ρ₁ n (Hp.op.obj i)
  letI := F₂.extCoefficientModule A₂ ρ₂ n (Hj.op.obj i)
  letI := F₂.extCoefficientModule A₂ ρ₂ n d
  letI := F₃.extCoefficientModule A₃ ρ₃ n (Ha.op.obj (Hp.op.obj i))
  letI := F₃.extCoefficientModule A₃ ρ₃ n (Hb.op.obj d)
  refine ModuleCat.extendAdditiveSquare σ s
    (F₀.extCoefficientModule A₀ ρ₀ n i)
    (F₁.extCoefficientModule A₁ ρ₁ n (Hp.op.obj i))
    (F₂.extCoefficientModule A₂ ρ₂ n (Hj.op.obj i))
    (F₃.extCoefficientModule A₃ ρ₃ n (Hb.op.obj d)) ?_ ?_ ?_ ?_
  · intro a x
    exact Lp.extCoefficientTransfer_smul F₀ F₁ Hp ep σ A₀ A₁ ρ₀ ρ₁ φp hp n i a x
  · intro a x
    exact Lj.extCoefficientTransfer_smul F₀ F₂ Hj ej (RingHom.id R)
      A₀ A₂ ρ₀ ρ₂ φj hj n i a x
  · intro a x
    change Ext.{max r w} (F₁.obj (Hp.op.obj i).unop) A₁ n at x
    change ((F₃.extModuleDiagram A₃ ρ₃ n).map κA)
        (La.extCoefficientTransfer (ea.inv.app (Hp.op.obj i).unop) φa n (a • x)) = _
    rw [La.extCoefficientTransfer_smul F₁ F₃ Ha ea (RingHom.id S)
      A₁ A₃ ρ₁ ρ₃ φa ha n (Hp.op.obj i) a x]
    exact ((F₃.extModuleDiagram A₃ ρ₃ n).map κA).hom.map_smul a _
  · intro a x
    change Ext.{max r w} (F₂.obj (Hj.op.obj i).unop) A₂ n at x
    change Lb.extCoefficientTransfer (eb.inv.app d.unop) φb n
      (((F₂.extModuleDiagram A₂ ρ₂ n).map κJ) (a • x)) = _
    exact (congrArg (Lb.extCoefficientTransfer (eb.inv.app d.unop) φb n)
      (((F₂.extModuleDiagram A₂ ρ₂ n).map κJ).hom.map_smul a x)).trans
        (Lb.extCoefficientTransfer_smul F₂ F₃ Hb eb σ A₂ A₃ ρ₂ ρ₃ φb hb n d a _)

/-- The top edge is the original whole-diagram scalar mate, at the same index. -/
theorem extScalarRestrictionSquare_top :
    (Lp.extScalarRestrictionSquare La Lj Lb F₀ F₁ F₂ F₃ Hp Ha Hj Hb ep ea ej eb
      φp φa φj φb n σ ρ₀ ρ₁ ρ₂ ρ₃ hp ha hj hb τ i κJ κA hk h).f₁₂ =
    (Lp.extScalarTensorDiagramMap F₀ F₁ Hp ep σ A₀ A₁ ρ₀ ρ₁ φp hp n).app i := by
  exact (CategoryTheory.Adjunction.whiskerRight_homEquiv_symm_app
    (ModuleCat.extendRestrictScalarsAdj.{max r w, r, r} σ)
      (F₀.extModuleDiagram A₀ ρ₀ n) (Hp.op ⋙ F₁.extModuleDiagram A₁ ρ₁ n)
      (Lp.extScalarDiagramMap F₀ F₁ Hp ep σ A₀ A₁ ρ₀ ρ₁ φp hp n) i).symm

/-- The lower edge is the original bottom mate after its actual source-index
transport; no top-open identification is silently substituted. -/
theorem extScalarRestrictionSquare_bottom :
    (Lp.extScalarRestrictionSquare La Lj Lb F₀ F₁ F₂ F₃ Hp Ha Hj Hb ep ea ej eb
      φp φa φj φb n σ ρ₀ ρ₁ ρ₂ ρ₃ hp ha hj hb τ i κJ κA hk h).f₃₄ =
    (ModuleCat.extendScalars σ).map ((F₂.extModuleDiagram A₂ ρ₂ n).map κJ) ≫
      (Lb.extScalarTensorDiagramMap F₂ F₃ Hb eb σ A₂ A₃ ρ₂ ρ₃ φb hb n).app d := by
  exact (CategoryTheory.Adjunction.homEquiv_naturality_left_symm
    (ModuleCat.extendRestrictScalarsAdj.{max r w, r, r} σ)
    ((F₂.extModuleDiagram A₂ ρ₂ n).map κJ)
      ((Lb.extScalarDiagramMap F₂ F₃ Hb eb σ A₂ A₃ ρ₂ ρ₃ φb hb n).app d)).trans
    (congrArg
      (fun f => (ModuleCat.extendScalars σ).map ((F₂.extModuleDiagram A₂ ρ₂ n).map κJ) ≫ f)
      (CategoryTheory.Adjunction.whiskerRight_homEquiv_symm_app
        (ModuleCat.extendRestrictScalarsAdj.{max r w, r, r} σ)
        (F₂.extModuleDiagram A₂ ρ₂ n) (Hb.op ⋙ F₃.extModuleDiagram A₃ ρ₃ n)
        (Lb.extScalarDiagramMap F₂ F₃ Hb eb σ A₂ A₃ ρ₂ ρ₃ φb hb n) d).symm)

end CategoryTheory.Functor
