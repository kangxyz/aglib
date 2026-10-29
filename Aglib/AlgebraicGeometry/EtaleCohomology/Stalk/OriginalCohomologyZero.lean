/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalCohomology
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedGammaZero

/-!
# Normalization of the original degree-zero cohomology comparison

Original degree-zero Ext classes are sent to the native derived-functor unit
applied to the original section. No independent comparison is chosen in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe u v w

namespace CategoryTheory.InjectiveResolution

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem representedExtZero_of_eq
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C] [HasExt.{w} C]
    (P M : C) (I : InjectiveResolution M)
    (H : C ⥤ AddCommGrpCat.{v})
    (e : (preadditiveCoyoneda.obj (op P)).rightDerived 0 ≅ H)
    (b : (preadditiveCoyoneda.obj (op P)).obj M ⟶ H.obj M)
    (hb : (preadditiveCoyoneda.obj (op P)).toRightDerivedZero.app M ≫ e.hom.app M = b)
    (a : P ⟶ M) (E : CategoryTheory.Abelian.Ext.{w} P M 0 ≃+ H.obj M)
    (hE : E = (I.extRightDerivedAddEquiv P 0).trans (e.app M).addCommGroupIsoToAddEquiv)
    (x : CategoryTheory.Abelian.Ext.{w} P M 0) (hx : x = CategoryTheory.Abelian.Ext.mk₀ a)
    (y : H.obj M) (hy : y = b a) : E x = y := by
  rw [hE, hx, hy]
  change e.hom.app M (I.extRightDerivedAddEquiv P 0 (CategoryTheory.Abelian.Ext.mk₀ a)) = b a
  rw [extRightDerivedAddEquiv_mk₀]
  exact ConcreteCategory.congr_hom hb a

end CategoryTheory.InjectiveResolution

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)

/-- The represented derived comparison preserves the original degree-zero unit. -/
theorem directImagePresheafRepresentedDerivedIso_zero_unit
    (F : AbelianSheaf.{u, u + 1} X) :
    (preadditiveCoyoneda.obj (op
        (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
          (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U)))).toRightDerivedZero.app F ≫
      (directImagePresheafRepresentedDerivedIso f U 0).hom.app F =
    (directImagePresheafRepresentedIso f U).hom.app F ≫
      ((directImagePresheaf f).toRightDerivedZero.app F).app (op U) := by
  have h₁ := Sheaf.ModuleCoefficients.toRightDerivedZero_naturality
    (directImagePresheafRepresentedIso f U).hom F
  have h₂ := Sheaf.ModuleCoefficients.toRightDerivedZero_postcomp
    (directImagePresheaf f) ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U)) F
  change _ ≫ (Sheaf.ModuleCoefficients.rightDerivedNatIso
      (directImagePresheafRepresentedIso f U) 0).hom.app F ≫
      (Sheaf.ModuleCoefficients.rightDerivedPostcompIso (directImagePresheaf f)
        ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U)) 0).hom.app F = _
  dsimp only [Sheaf.ModuleCoefficients.rightDerivedNatIso,
    CategoryTheory.Functor.rightDerivedNatIsoOfAdditive]
  rw [← Category.assoc, h₁, Category.assoc, h₂]
  rfl

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Original degree-zero Ext sections retain their actual section under the
native unit into the resolution cohomology presheaf. -/
theorem originalCohomologyResolutionEquiv_mk₀
    (F : AbelianSheaf.{u, u + 1} X)
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) ⟶ F) :
    originalCohomologyResolutionEquiv f U F 0 (CategoryTheory.Abelian.Ext.mk₀ a) =
      ((directImagePresheaf f).toRightDerivedZero.app F).app (op U)
        (Sheaf.Hypercohomology.sectionsAddEquiv
          (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) F a) := by
  exact CategoryTheory.InjectiveResolution.representedExtZero_of_eq
    (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U)) F (injectiveResolution F)
    (resolutionCohomologyPresheaf f 0 ⋙
      (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U))
    (directImagePresheafRepresentedDerivedIso f U 0)
    ((directImagePresheafRepresentedIso f U).hom.app F ≫
      ((directImagePresheaf f).toRightDerivedZero.app F).app (op U))
    (directImagePresheafRepresentedDerivedIso_zero_unit f U F) a
    (originalCohomologyResolutionEquiv f U F 0) rfl
    (CategoryTheory.Abelian.Ext.mk₀ a) rfl
    (((directImagePresheaf f).toRightDerivedZero.app F).app (op U)
      (Sheaf.Hypercohomology.sectionsAddEquiv
        (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) F a)) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
