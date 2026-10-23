/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalCohomology
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ExtSourceNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ExactPostcomposition
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Naturality

/-! # Original restriction maps for higher direct-image cohomology -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe u v u₁ v₁ u₂ v₂ w

namespace CategoryTheory.Sheaf.ModuleCoefficients

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem representedPostcomp_restriction
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u₁} [Category.{v₁} D] [Abelian D]
    {E : Type u₂} [Category.{v₂} E] [Abelian E]
    (F : C ⥤ D) [F.Additive] {G H : D ⥤ E}
    [G.Additive] [H.Additive] [G.PreservesHomology] [H.PreservesHomology]
    {P Q : C ⥤ E} [P.Additive] [Q.Additive]
    (p : P ⟶ Q) (τ : G ⟶ H) (α : P ≅ F ⋙ G) (β : Q ≅ F ⋙ H)
    (h : p ≫ β.hom = α.hom ≫ Functor.whiskerLeft F τ) (q : ℕ) (M : C) :
    (p.rightDerived q).app M ≫
        (rightDerivedNatIso β q ≪≫ rightDerivedPostcompIso F H q).hom.app M =
      (rightDerivedNatIso α q ≪≫ rightDerivedPostcompIso F G q).hom.app M ≫
        τ.app ((F.rightDerived q).obj M) := by
  have hd := congrArg (fun a => NatTrans.rightDerived a q) h
  rw [NatTrans.rightDerived_comp, NatTrans.rightDerived_comp] at hd
  have hc := congrArg (fun a => a.app M) hd
  dsimp only [NatTrans.comp_app] at hc
  dsimp only [Iso.trans_hom, NatTrans.comp_app, rightDerivedNatIso]
  rw [← Category.assoc, hc, Category.assoc, rightDerivedPostcompIso_hom_natTrans]
  exact (Category.assoc _ _ _).symm

private theorem representedRestriction_of_eq
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C] [HasExt.{w} C]
    {P Q M : C} (p : Q ⟶ P) (I : InjectiveResolution M) (q : ℕ)
    {H₀ H₁ : C ⥤ AddCommGrpCat.{v}}
    (e₀ : (preadditiveCoyoneda.obj (op P)).rightDerived q ≅ H₀)
    (e₁ : (preadditiveCoyoneda.obj (op Q)).rightDerived q ≅ H₁)
    (r : H₀.obj M ⟶ H₁.obj M)
    (he : ((preadditiveCoyoneda.map p.op).rightDerived q).app M ≫ e₁.hom.app M =
      e₀.hom.app M ≫ r)
    (E₀ : CategoryTheory.Abelian.Ext.{w} P M q ≃+ H₀.obj M)
    (E₁ : CategoryTheory.Abelian.Ext.{w} Q M q ≃+ H₁.obj M)
    (h₀ : E₀ = (I.extRightDerivedAddEquiv P q).trans (e₀.app M).addCommGroupIsoToAddEquiv)
    (h₁ : E₁ = (I.extRightDerivedAddEquiv Q q).trans (e₁.app M).addCommGroupIsoToAddEquiv)
    (x : CategoryTheory.Abelian.Ext.{w} P M q)
    (y : CategoryTheory.Abelian.Ext.{w} Q M q)
    (hy : y = (CategoryTheory.Abelian.Ext.mk₀ p).comp x (zero_add q)) :
    E₁ y = r (E₀ x) := by
  rw [h₀, h₁, hy]
  change e₁.hom.app M
    (I.extRightDerivedAddEquiv Q q
      ((CategoryTheory.Abelian.Ext.mk₀ p).comp x (zero_add q))) =
    r (e₀.hom.app M (I.extRightDerivedAddEquiv P q x))
  rw [I.extRightDerivedAddEquiv_naturality_left P q p x]
  exact ConcreteCategory.congr_hom he (I.extRightDerivedAddEquiv P q x)

end CategoryTheory.Sheaf.ModuleCoefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Etale} (g : V ⟶ U)

/-- The actual represented section comparisons respect original étale restrictions. -/
theorem directImagePresheafRepresentedIso_restriction :
    preadditiveCoyoneda.map
        (((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1}
          (Scheme.smallEtaleTopology X)).map ((siteBaseChange f).map g)).op) ≫
      (directImagePresheafRepresentedIso f V).hom =
    (directImagePresheafRepresentedIso f U).hom ≫
      Functor.whiskerLeft (directImagePresheaf f)
        ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).map g.op) := by
  ext F a
  exact Sheaf.SliceCohomology.freeSections_naturality
    (Scheme.smallEtaleTopology X) ((siteBaseChange f).map g) F a

/-- Native represented-derived comparisons respect the original restriction map. -/
theorem directImagePresheafRepresentedDerivedIso_restriction (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) :
    ((preadditiveCoyoneda.map
        (((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1}
          (Scheme.smallEtaleTopology X)).map
            ((siteBaseChange f).map g)).op)).rightDerived q).app F ≫
      (directImagePresheafRepresentedDerivedIso f V q).hom.app F =
    (directImagePresheafRepresentedDerivedIso f U q).hom.app F ≫
      ((resolutionCohomologyPresheaf f q).obj F).map g.op :=
  Sheaf.ModuleCoefficients.representedPostcomp_restriction
    (directImagePresheaf f) _
    ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).map g.op)
    (directImagePresheafRepresentedIso f U) (directImagePresheafRepresentedIso f V)
    (directImagePresheafRepresentedIso_restriction f g) q F

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Restriction of original Ext cohomology is the actual resolution-presheaf restriction. -/
theorem originalCohomologyResolutionEquiv_restriction
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    originalCohomologyResolutionEquiv f V F q
      ((Sheaf.LargeCohomology.presheaf.{w, u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) F q).map ((siteBaseChange f).map g).op x) =
      ((resolutionCohomologyPresheaf f q).obj F).map g.op
        (originalCohomologyResolutionEquiv f U F q x) := by
  exact Sheaf.ModuleCoefficients.representedRestriction_of_eq
    ((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1}
      (Scheme.smallEtaleTopology X)).map ((siteBaseChange f).map g))
    (injectiveResolution F) q
    (directImagePresheafRepresentedDerivedIso f U q)
    (directImagePresheafRepresentedDerivedIso f V q)
    (((resolutionCohomologyPresheaf f q).obj F).map g.op)
    (directImagePresheafRepresentedDerivedIso_restriction f g q F)
    (originalCohomologyResolutionEquiv f U F q)
    (originalCohomologyResolutionEquiv f V F q) rfl rfl x _ rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
