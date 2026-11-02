/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Pullback
public import Aglib.CategoryTheory.Sites.Pullback.Coefficients
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Underlying
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# The original abelian inverse image underlying constant-ring pullback

This comparison is between the native ringed pullback and the original étale
abelian inverse image. Coefficient forgetting is the existing `forget₂`, and
its comparison is the preserved-Kan/sheafification comparison. No duplicate
scalar-forgetting construction or changed site is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.TorsionZMod.Ringed

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- Additive forgetting preserves the actual sheafification class, detected on underlying types. -/
theorem moduleForget_preservesSheafification :
    (Scheme.smallEtaleTopology X).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleCat.Sheaf.forget_preservesSheafification Λ (Scheme.smallEtaleTopology X)

attribute [local instance] moduleForget_preservesSheafification

/-- The inverse equivalence retains the same original abelian sheaf. -/
def moduleSheafInverseUnderlyingIso :
    (moduleSheafEquivalence X Λ).inverse ⋙
      sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      SheafOfModules.toSheaf (constantRing X Λ) :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafInverseUnderlyingIso.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ

variable {X} {S : Scheme.{u}} (f : S ⟶ X)

/-- Additive forgetting preserves the actual Kan extensions at the original site sizes. -/
theorem moduleForget_preservesLeftKanExtensions :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions
      (siteBaseChange f).op := by
  intro P
  infer_instance

attribute [local instance] moduleForget_preservesLeftKanExtensions

/-- The original module-valued inverse image commutes with additive forgetting. -/
def moduleValuedInverseImageUnderlyingIso :
    moduleValuedInverseImage f Λ ⋙
      sheafCompose (Scheme.smallEtaleTopology S)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
    sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ inverseImage f :=
  ModuleCat.Sheaf.ConstantRing.moduleValuedInverseImageUnderlyingIso.{
    u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- The native constant-ring inverse image has the original abelian inverse image underneath. -/
def moduleInverseImageUnderlyingIso :
    moduleInverseImage f Λ ⋙ SheafOfModules.toSheaf (constantRing S Λ) ≅
      SheafOfModules.toSheaf (constantRing X Λ) ⋙ inverseImage f :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImageUnderlyingIso.{
    u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- The thin inverse-equivalence realization retains its original four factors. -/
theorem moduleSheafInverseUnderlyingIso_eq_original : moduleSheafInverseUnderlyingIso X Λ =
    Functor.isoWhiskerLeft (moduleSheafEquivalence X Λ).inverse
      (moduleSheafUnderlyingIso X Λ).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafEquivalence X Λ).counitIso
      (SheafOfModules.toSheaf (constantRing X Λ)) ≪≫ Functor.leftUnitor _ :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafInverseUnderlyingIso_eq_original.{
    u + 1, u, u + 1, u + 1} (Scheme.smallEtaleTopology X) Λ

/-- The thin native inverse-image realization retains its original seven factors. -/
theorem moduleInverseImageUnderlyingIso_eq_original : moduleInverseImageUnderlyingIso Λ f =
    Functor.isoWhiskerRight (moduleInverseImageTransportIso f Λ)
      (SheafOfModules.toSheaf (constantRing S Λ)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((moduleSheafEquivalence X Λ).inverse ⋙ moduleValuedInverseImage f Λ)
      (moduleSheafUnderlyingIso S Λ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleSheafEquivalence X Λ).inverse
      (moduleValuedInverseImageUnderlyingIso Λ f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafInverseUnderlyingIso X Λ) (inverseImage f) :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImageUnderlyingIso_eq_original.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
