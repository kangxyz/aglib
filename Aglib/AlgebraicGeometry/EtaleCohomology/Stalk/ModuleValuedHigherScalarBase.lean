/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ModuleValuedHigherUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ModuleHigherScalarAction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.ScalarEquivalence
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.UnderlyingAction

/-! # The original valued higher-image comparison preserves noncentral scalars

The native coefficient equivalences and original ringed comparison are used
without changing any derived realization or higher-image map. The constant
coefficient specialization is checked in a separate thin consumer.
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

/-- The original valued higher-image underlying comparison is scalar-equivariant. -/
theorem moduleValuedHigherDirectImageUnderlyingIso_scalar (q : ℕ) (a : Λ) :
    Functor.whiskerLeft ((moduleValuedDirectImage f Λ).rightDerived q)
        (ModuleCat.Sheaf.underlyingScalar S.smallEtaleTopology Λ a) ≫
      (moduleValuedHigherDirectImageUnderlyingIso f Λ q).hom =
    (moduleValuedHigherDirectImageUnderlyingIso f Λ q).hom ≫
      Functor.whiskerRight (ModuleCat.Sheaf.underlyingScalar X.smallEtaleTopology Λ a)
        (higherDirectImage f q) := by
  apply NatTrans.ext
  funext F
  let N := ((moduleDirectImage f Λ).rightDerived q).obj
    ((moduleSheafEquivalence X Λ).functor.obj F)
  let c := (ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology).map
    ((moduleHigherDirectImageValuedComparison f Λ q).inv.app F)
  let d := (moduleSheafInverseUnderlyingIso S Λ).hom.app N
  let e := (moduleHigherDirectImageUnderlyingIso Λ f q).hom.app
    ((moduleSheafEquivalence X Λ).functor.obj F)
  let g := (higherDirectImage f q).map ((moduleSheafUnderlyingIso X Λ).hom.app F)
  let σ := ModuleCat.Sheaf.underlyingScalar S.smallEtaleTopology Λ a
  have hc := (σ.naturality ((moduleHigherDirectImageValuedComparison f Λ q).inv.app F)).symm
  have hd := NatTrans.congr_app
    (ModuleCat.Sheaf.ConstantRing.moduleSheafInverseUnderlyingIso_scalar.{
      u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ a) N
  have he := NatTrans.congr_app (moduleHigherDirectImageUnderlyingIso_scalar Λ f q a)
    ((moduleSheafEquivalence X Λ).functor.obj F)
  have hg₀ := NatTrans.congr_app
    (ModuleCat.Sheaf.ConstantRing.moduleSheafUnderlyingIso_scalar.{
      u + 1, u, u + 1, u + 1} X.smallEtaleTopology Λ a) F
  change (moduleUnderlyingScalar Λ X a).app
      ((moduleSheafEquivalence X Λ).functor.obj F) ≫
        (moduleSheafUnderlyingIso X Λ).hom.app F =
    (moduleSheafUnderlyingIso X Λ).hom.app F ≫
      (ModuleCat.Sheaf.underlyingScalar X.smallEtaleTopology Λ a).app F at hg₀
  have hg := congrArg (higherDirectImage f q).map hg₀
  rw [Functor.map_comp, Functor.map_comp] at hg
  simp only [moduleValuedHigherDirectImageUnderlyingIso, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.assoc]
  change σ.app (((moduleValuedDirectImage f Λ).rightDerived q).obj F) ≫ c ≫ d ≫ e ≫ g =
    c ≫ d ≫ e ≫ g ≫ (higherDirectImage f q).map
      ((ModuleCat.Sheaf.underlyingScalar X.smallEtaleTopology Λ a).app F)
  change σ.app (((moduleValuedDirectImage f Λ).rightDerived q).obj F) ≫ c =
    c ≫ σ.app ((moduleSheafEquivalence S Λ).inverse.obj N) at hc
  change σ.app ((moduleSheafEquivalence S Λ).inverse.obj N) ≫ d =
    d ≫ (moduleUnderlyingScalar Λ S a).app N at hd
  change (moduleUnderlyingScalar Λ S a).app N ≫ e =
    e ≫ (higherDirectImage f q).map
      ((moduleUnderlyingScalar Λ X a).app ((moduleSheafEquivalence X Λ).functor.obj F)) at he
  change (higherDirectImage f q).map
      ((moduleUnderlyingScalar Λ X a).app ((moduleSheafEquivalence X Λ).functor.obj F)) ≫ g =
    g ≫ (higherDirectImage f q).map
      ((ModuleCat.Sheaf.underlyingScalar X.smallEtaleTopology Λ a).app F) at hg
  rw [← Category.assoc _ c, hc, Category.assoc,
    ← Category.assoc _ d, hd, Category.assoc,
    ← Category.assoc _ e, he, Category.assoc, hg]


end AlgebraicGeometry.Scheme.EtaleCohomology
