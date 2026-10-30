/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Over.SitePullbackPasting
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Opposites

/-! # Original pullback-chart transitions and coefficient naturality

The selected property-Over pullback, compositor, symmetry and representative
arrow construct the original transition. Its whole underlying value is proved
from both original projections. Coefficients are arbitrary natural
transformations, with no invented invertibility or new chart realization.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

/-- An arbitrary original presheaf transformation respects actual chart isos. -/
theorem presheafTransition_chartIso {C D A : Type*}
    [Category* C] [Category* D] [Category* A]
    (K : C ⥤ D) (P : Cᵒᵖ ⥤ A) (Q : Dᵒᵖ ⥤ A) (η : P ⟶ K.op ⋙ Q)
    {U U' : C} {V V' : D} (e : U ≅ U') (e' : V ≅ V')
    (c : V' ⟶ K.obj U') (a : V ⟶ K.obj U)
    (ha : e'.inv ≫ a = c ≫ K.map e.inv) :
    η.app (op U) ≫ Q.map a.op ≫ Q.map e'.inv.op =
      P.map e.inv.op ≫ η.app (op U') ≫ Q.map c.op := by
  have hm : Q.map a.op ≫ Q.map e'.inv.op = Q.map ((K.map e.inv).op) ≫ Q.map c.op :=
    (Q.map_comp _ _).symm.trans
      ((congrArg (fun f => Q.map f.op) ha).trans (Q.map_comp _ _))
  have hn : η.app (op U) ≫ Q.map ((K.map e.inv).op) =
      P.map e.inv.op ≫ η.app (op U') := (η.naturality e.inv.op).symm
  exact (congrArg (fun f => η.app (op U) ≫ f) hm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ Q.map c.op) hn).trans (Category.assoc _ _ _)))

end CategoryTheory.Functor

namespace CategoryTheory.MorphismProperty.Over.ChartTransition

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (P : MorphismProperty C) [P.IsStableUnderBaseChange]

/-- The original chart in its geometric pullback orientation. -/
def chart {X Y : C} (f : Y ⟶ X) (U : P.Over ⊤ X) : P.Over ⊤ Y :=
  MorphismProperty.Over.mk ⊤ (pullback.fst f U.hom) (P.pullback_fst f U.hom U.prop)

/-- Only the native pullback symmetry changes to the site orientation. -/
def chartIso {X Y : C} (f : Y ⟶ X) (U : P.Over ⊤ X) :
    chart P f U ≅ (MorphismProperty.Over.pullback P ⊤ f).obj U :=
  MorphismProperty.Over.isoMk (pullbackSymmetry f U.hom)
    (pullbackSymmetry_hom_comp_snd _ _)

/-- The actual site compositor with the original triangle equality transport. -/
def triangleIso {X Y Z : C} (f : Y ⟶ X) (p : Z ⟶ X) (g : Z ⟶ Y) (h : g ≫ f = p) :
    MorphismProperty.Over.pullback P ⊤ p ≅
      MorphismProperty.Over.pullback P ⊤ f ⋙ MorphismProperty.Over.pullback P ⊤ g :=
  eqToIso (congrArg (fun k : Z ⟶ X => MorphismProperty.Over.pullback P ⊤ k) h.symm) ≪≫
    MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) g f

/-- The whole original triangle comparison preserves its nested source projection. -/
@[reassoc]
theorem triangleIso_hom_fst_fst {X Y Z : C}
    (f : Y ⟶ X) (p : Z ⟶ X) (g : Z ⟶ Y) (h : g ≫ f = p) (U : P.Over ⊤ X) :
    ((triangleIso P f p g h).hom.app U).left ≫
      pullback.fst (pullback.snd U.hom f) g ≫ pullback.fst U.hom f =
        pullback.fst U.hom p := by
  subst p
  simpa only [triangleIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, eqToHom_refl, Category.id_comp] using
      MorphismProperty.Over.pullbackComp_left_fst_fst (P := P) (Q := ⊤) g f U

/-- The same original comparison preserves its nested base projection. -/
@[reassoc]
theorem triangleIso_hom_fst_snd {X Y Z : C}
    (f : Y ⟶ X) (p : Z ⟶ X) (g : Z ⟶ Y) (h : g ≫ f = p) (U : P.Over ⊤ X) :
    ((triangleIso P f p g h).hom.app U).left ≫
      pullback.fst (pullback.snd U.hom f) g ≫ pullback.snd U.hom f =
        pullback.snd U.hom p ≫ g := by
  let a : Limits.pullback U.hom p ⟶ Limits.pullback (pullback.snd U.hom f) g :=
    ((triangleIso P f p g h).hom.app U).left
  have ha : a ≫ pullback.snd (pullback.snd U.hom f) g = pullback.snd U.hom p :=
    MorphismProperty.Over.w ((triangleIso P f p g h).hom.app U)
  calc
    a ≫ pullback.fst (pullback.snd U.hom f) g ≫ pullback.snd U.hom f =
        a ≫ (pullback.snd (pullback.snd U.hom f) g ≫ g) := by
      exact congrArg (fun z => a ≫ z)
        (pullback.condition (f := pullback.snd U.hom f) (g := g))
    _ = (a ≫ pullback.snd (pullback.snd U.hom f) g) ≫ g :=
      (Category.assoc _ _ _).symm
    _ = pullback.snd U.hom p ≫ g := congrArg (fun z => z ≫ g) ha

/-- The SAME representative arrow, with its original first projection. -/
def representativeArrow {X Y : C} (f : Y ⟶ X) {U : P.Over ⊤ X} {W : P.Over ⊤ Y}
    (a : W ⟶ (MorphismProperty.Over.pullback P ⊤ f).obj U) :
    CategoryTheory.Over.mk (W.hom ≫ f) ⟶ CategoryTheory.Over.mk U.hom :=
  CategoryTheory.Over.homMk (a.left ≫ pullback.fst U.hom f) (by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => a.left ≫ k) (pullback.condition (f := U.hom) (g := f))).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ f) (MorphismProperty.Over.w a)))))

/-- Construct the actual original test arrow from symmetry and the native compositor. -/
def testArrow {X Y Z : C}
    (f : Y ⟶ X) (p : Z ⟶ X) (g : Z ⟶ Y) (h : g ≫ f = p) (U : P.Over ⊤ X) :
    chart P p U ⟶ (MorphismProperty.Over.pullback P ⊤ g).obj (chart P f U) :=
  (chartIso P p U).hom ≫ (triangleIso P f p g h).hom.app U ≫
    (MorphismProperty.Over.pullback P ⊤ g).map (chartIso P f U).inv

/-- The complete original chart arrow has the original Over-pullback transition value. -/
theorem representative_testArrow_left {X Y Z : C}
    (f : Y ⟶ X) (p : Z ⟶ X) (g : Z ⟶ Y) (h : g ≫ f = p) (U : P.Over ⊤ X) :
    (representativeArrow P g (testArrow P f p g h U)).left =
      ((CategoryTheory.Over.pullback U.hom).map
        (show CategoryTheory.Over.mk p ⟶ CategoryTheory.Over.mk f from
          CategoryTheory.Over.homMk g h)).left := by
  apply pullback.hom_ext
  · exact (CategoryTheory.Over.w (representativeArrow P g (testArrow P f p g h U))).trans
      (pullback.lift_fst _ _ _).symm
  · let ε : Limits.pullback p U.hom ⟶ Limits.pullback U.hom p := (chartIso P p U).hom.left
    let τ : Limits.pullback U.hom p ⟶ Limits.pullback (pullback.snd U.hom f) g :=
      ((triangleIso P f p g h).hom.app U).left
    let μ : Limits.pullback (pullback.snd U.hom f) g ⟶ Limits.pullback (pullback.fst f U.hom) g :=
      ((MorphismProperty.Over.pullback P ⊤ g).map (chartIso P f U).inv).left
    let ρ : Limits.pullback (pullback.fst f U.hom) g ⟶ Limits.pullback f U.hom :=
      pullback.fst (chart P f U).hom g
    let σ : Limits.pullback f U.hom ⟶ U.left := pullback.snd f U.hom
    let π : Limits.pullback (pullback.snd U.hom f) g ⟶ Limits.pullback U.hom f :=
      pullback.fst (pullback.snd U.hom f) g
    have hμ : μ ≫ ρ = π ≫ (chartIso P f U).inv.left := pullback.lift_fst _ _ _
    have hσ : (chartIso P f U).inv.left ≫ σ = pullback.fst U.hom f :=
      pullbackSymmetry_inv_comp_snd _ _
    have hm : μ ≫ ρ ≫ σ = π ≫ pullback.fst U.hom f :=
      (Category.assoc μ ρ σ).symm.trans
        ((congrArg (fun z => z ≫ σ) hμ).trans
          ((Category.assoc _ _ _).trans (congrArg (fun z => π ≫ z) hσ)))
    have ht : τ ≫ π ≫ pullback.fst U.hom f = pullback.fst U.hom p :=
      triangleIso_hom_fst_fst P f p g h U
    have he : ε ≫ pullback.fst U.hom p = pullback.snd p U.hom :=
      pullbackSymmetry_hom_comp_fst _ _
    change ((ε ≫ τ ≫ μ) ≫ ρ) ≫ σ = _
    exact (Category.assoc _ _ _).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => ε ≫ z) (Category.assoc τ μ (ρ ≫ σ))).trans
          ((congrArg (fun z => ε ≫ τ ≫ z) hm).trans
            ((congrArg (fun z => ε ≫ z) ht).trans
              (he.trans (pullback.lift_snd _ _ _).symm)))))

end CategoryTheory.MorphismProperty.Over.ChartTransition
