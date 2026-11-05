/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ModuleValuedHigherScalarBase
public import Aglib.CategoryTheory.Sites.ConstantSheaf.CompositionNaturality
public import Aglib.CategoryTheory.Functor.ComparisonAction

/-! # The original valued higher-image comparison preserves noncentral scalars

The native coefficient equivalences and original ringed comparison are used
without changing any derived realization or higher-image map.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u wMX wMS wAX wAS
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  ModuleCat.Sheaf.forget_preservesSheafification
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard
  constantRingModuleSheaf_enoughInjectives valuedSheaf_enoughInjectives
  valuedDirectImage_additive
open Coefficients
variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

/-- Constant coefficients retain the same original scalar square after higher image. -/
theorem constantModuleValuedHigherDirectImageUnderlyingIso_scalar
    (q : ℕ) (M : ModuleCat.{u + 1} Λ) (a : Λ) :
    (ModuleCat.Sheaf.underlyingScalar S.smallEtaleTopology Λ a).app
        ((constantModuleValuedHigherDirectImage f Λ q).obj M) ≫
      (constantModuleValuedHigherDirectImageUnderlyingIso f Λ q).hom.app M =
    (constantModuleValuedHigherDirectImageUnderlyingIso f Λ q).hom.app M ≫
      (higherDirectImage f q).map
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((ModuleCat.forgetScalar Λ a).app M)) := by
  let I := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let V := ModuleCat.Sheaf.underlying Λ X.smallEtaleTopology
  let J := constantModuleUnderlying (X := X) Λ
  let c := ModuleCat.Sheaf.constantUnderlyingIso Λ X.smallEtaleTopology
  let β := ModuleCat.Sheaf.underlyingScalar X.smallEtaleTopology Λ a
  let γ := Functor.whiskerRight (ModuleCat.forgetScalar Λ a)
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  have hc : Functor.whiskerLeft I β ≫ c.hom = c.hom ≫ γ := by
    apply NatTrans.ext
    funext N
    exact constantCommuteCompose_coefficient_naturality X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      (ModuleCat.forgetScalar Λ a) N
  exact NatTrans.congr_app
    (Functor.whiskeredComparison_action I ((moduleValuedDirectImage f Λ).rightDerived q)
      (ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology) V (higherDirectImage f q) J
      (moduleValuedHigherDirectImageUnderlyingIso f Λ q) c
      (ModuleCat.Sheaf.underlyingScalar S.smallEtaleTopology Λ a) β γ
      (moduleValuedHigherDirectImageUnderlyingIso_scalar f Λ q a) hc) M

end AlgebraicGeometry.Scheme.EtaleCohomology
