/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.RightDerived.Represented
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ExtSourceNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedGammaZero
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ExactPostcomposition

/-! # Original represented Ext and exact postcomposition values

The existing represented/postcomposition constructor retains the actual
right-derived zero unit and whole source naturality. Supplied-resolution Ext
comparisons use that same constructor directly. No arbitrary comparison E,
postulated derived square, auxiliary value or reference realization is input.
The Ext universe is independent of the original represented Hom world.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Preadditive Opposite

namespace CategoryTheory

universe s

/-- Evaluate the same complete raw group equation before substituting derived carriers. -/
private theorem rawRepresentedSquare_apply
    {A B C D : AddCommGrpCat.{s}} (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (x : A) : g (f x) = k (h x) :=
  ConcreteCategory.congr_hom w x

end CategoryTheory

namespace CategoryTheory.Functor

universe uC vC uD vD e

variable {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]
  (G : D ⥤ AddCommGrpCat.{vC}) [G.Additive] [G.PreservesHomology]
  {P : C} (α : additiveGamma P ≅ F ⋙ G)

/-- The existing whole represented postcomposition Iso retains its original zero unit. -/
@[reassoc]
theorem representedRightDerivedPostcompIso_zero_unit (M : C) :
    (additiveGamma P).toRightDerivedZero.app M ≫
        (representedRightDerivedPostcompIso P F G α 0).inv.app M =
      α.hom.app M ≫ G.map (F.toRightDerivedZero.app M) := by
  have h₁ := Sheaf.ModuleCoefficients.toRightDerivedZero_naturality α.hom M
  have h₂ := Sheaf.ModuleCoefficients.toRightDerivedZero_postcomp F G M
  change _ ≫ (Sheaf.ModuleCoefficients.rightDerivedNatIso α 0).hom.app M ≫
    (Sheaf.ModuleCoefficients.rightDerivedPostcompIso F G 0).hom.app M = _
  dsimp only [Sheaf.ModuleCoefficients.rightDerivedNatIso, rightDerivedNatIsoOfAdditive]
  rw [← Category.assoc, h₁, Category.assoc, h₂]

variable {G}

/-- An ordinary represented-source square gives the whole derived restriction square. -/
theorem representedRightDerivedPostcompIso_source
    {H : D ⥤ AddCommGrpCat.{vC}} [H.Additive] [H.PreservesHomology]
    {Q : C} (p : Q ⟶ P) (τ : G ⟶ H) (β : additiveGamma Q ≅ F ⋙ H)
    (h : preadditiveCoyoneda.map p.op ≫ β.hom = α.hom ≫ Functor.whiskerLeft F τ) (n : ℕ) :
    (preadditiveCoyoneda.map p.op).rightDerived n ≫
        (representedRightDerivedPostcompIso Q F H β n).inv =
      (representedRightDerivedPostcompIso P F G α n).inv ≫
        Functor.whiskerLeft (F.rightDerived n) τ := by
  apply NatTrans.ext
  funext M
  have hd := congrArg (fun a => NatTrans.rightDerived a n) h
  rw [NatTrans.rightDerived_comp, NatTrans.rightDerived_comp] at hd
  have hc := congrArg (fun a => a.app M) hd
  dsimp only [NatTrans.comp_app] at hc
  change ((preadditiveCoyoneda.map p.op).rightDerived n).app M ≫
      (Sheaf.ModuleCoefficients.rightDerivedNatIso β n ≪≫
        Sheaf.ModuleCoefficients.rightDerivedPostcompIso F H n).hom.app M =
    (Sheaf.ModuleCoefficients.rightDerivedNatIso α n ≪≫
        Sheaf.ModuleCoefficients.rightDerivedPostcompIso F G n).hom.app M ≫
      τ.app ((F.rightDerived n).obj M)
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Sheaf.ModuleCoefficients.rightDerivedNatIso,
    rightDerivedNatIsoOfAdditive]
  rw [← Category.assoc, hc, Category.assoc,
    Sheaf.ModuleCoefficients.rightDerivedPostcompIso_hom_natTrans]
  exact (Category.assoc _ _ _).symm

end CategoryTheory.Functor

namespace CategoryTheory.InjectiveResolution

universe uC vC uD vD e

variable {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C] [HasExt.{e} C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {M : C} (I : InjectiveResolution M) (P : C) (F : C ⥤ D) [F.Additive]
  (G : D ⥤ AddCommGrpCat.{vC}) [G.Additive] [G.PreservesHomology]
  (α : additiveGamma P ≅ F ⋙ G)

/-- The original supplied-resolution Ext comparison through the existing represented constructor. -/
def extRightDerivedPostcompAddEquiv (n : ℕ) : Ext.{e} P M n ≃+ G.obj ((F.rightDerived n).obj M) :=
  (I.extRightDerivedAddEquiv P n).trans
    ((Functor.representedRightDerivedPostcompIso P F G α n).symm.app M).addCommGroupIsoToAddEquiv

/-- The same original zero class maps to the actual derived unit on its represented section. -/
theorem extRightDerivedPostcompAddEquiv_mk₀ (a : P ⟶ M) :
    I.extRightDerivedPostcompAddEquiv P F G α 0 (Ext.mk₀ a) =
      G.map (F.toRightDerivedZero.app M) (α.hom.app M a) := by
  change (Functor.representedRightDerivedPostcompIso P F G α 0).inv.app M
      (I.extRightDerivedAddEquiv P 0 (Ext.mk₀ a)) = _
  rw [extRightDerivedAddEquiv_mk₀]
  have hunit := Functor.representedRightDerivedPostcompIso_zero_unit F G α M
  have hvalue := rawRepresentedSquare_apply
    ((additiveGamma P).toRightDerivedZero.app M)
    ((Functor.representedRightDerivedPostcompIso P F G α 0).inv.app M)
    (α.hom.app M) (G.map (F.toRightDerivedZero.app M)) hunit a
  exact hvalue

variable {G}

/-- Source restriction of original Ext is the actual exact-postcomposition restriction. -/
theorem extRightDerivedPostcompAddEquiv_source
    {H : D ⥤ AddCommGrpCat.{vC}} [H.Additive] [H.PreservesHomology]
    {Q : C} (p : Q ⟶ P) (τ : G ⟶ H) (β : additiveGamma Q ≅ F ⋙ H)
    (h : preadditiveCoyoneda.map p.op ≫ β.hom = α.hom ≫ Functor.whiskerLeft F τ)
    (n : ℕ) (x : Ext.{e} P M n) :
    I.extRightDerivedPostcompAddEquiv Q F H β n ((Ext.mk₀ p).comp x (zero_add n)) =
      τ.app ((F.rightDerived n).obj M) (I.extRightDerivedPostcompAddEquiv P F G α n x) := by
  change (Functor.representedRightDerivedPostcompIso Q F H β n).inv.app M
      (I.extRightDerivedAddEquiv Q n ((Ext.mk₀ p).comp x (zero_add n))) =
    τ.app ((F.rightDerived n).obj M)
      ((Functor.representedRightDerivedPostcompIso P F G α n).inv.app M
        (I.extRightDerivedAddEquiv P n x))
  rw [I.extRightDerivedAddEquiv_naturality_left P n p x]
  have hsource := Functor.representedRightDerivedPostcompIso_source F α p τ β h n
  have hcomponent := NatTrans.congr_app hsource M
  exact rawRepresentedSquare_apply (((preadditiveCoyoneda.map p.op).rightDerived n).app M)
    ((Functor.representedRightDerivedPostcompIso Q F H β n).inv.app M)
    ((Functor.representedRightDerivedPostcompIso P F G α n).inv.app M)
    (τ.app ((F.rightDerived n).obj M)) hcomponent (I.extRightDerivedAddEquiv P n x)

end CategoryTheory.InjectiveResolution
