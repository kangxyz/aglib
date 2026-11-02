/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Exactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact native constant-ring inverse image

Finite limits are detected by the original additive sheaf functor. The
proved underlying comparison transfers the original étale inverse image's
left exactness to the native ringed pullback. Injective preservation then
follows from the actual ringed adjunction, not from coefficient forgetting.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

attribute [local instance] hasSheafifyModules
  moduleForget_preservesSheafification
  moduleForget_preservesLeftKanExtensions
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard


variable {X S : Scheme.{u}} (f : S ⟶ X) (Λ : Type (u + 1)) [Ring Λ]

local instance nativeModuleAbelianPullback_preservesFiniteLimits :
    PreservesFiniteLimits ((siteBaseChange f).sheafPullback AddCommGrpCat.{u + 1}
      X.smallEtaleTopology S.smallEtaleTopology) :=
  inverseImage_preservesFiniteLimits f

instance moduleInverseImage_isLeftAdjoint : (moduleInverseImage f Λ).IsLeftAdjoint :=
  (moduleInverseImageAdjunction f Λ).isLeftAdjoint

instance moduleInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (moduleInverseImage f Λ) :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImage_preservesFiniteLimits.{
    u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

instance moduleInverseImage_preservesColimits :
    PreservesColimits (moduleInverseImage f Λ) := by infer_instance

instance moduleInverseImage_additive : (moduleInverseImage f Λ).Additive :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImage_additive.{
    u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

instance moduleDirectImage_additive : (moduleDirectImage f Λ).Additive :=
  (moduleInverseImageAdjunction f Λ).right_adjoint_additive

instance moduleInverseImage_preservesHomology :
    (moduleInverseImage f Λ).PreservesHomology :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImage_preservesHomology.{
    u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- The actual ringed inverse image preserves short exact sequences. -/
theorem shortExact_moduleInverseImage {T : ShortComplex (ModuleSheaf X Λ)}
    (hT : T.ShortExact) : (T.map (moduleInverseImage f Λ)).ShortExact :=
  hT.map_of_exact (moduleInverseImage f Λ)

/-- The original ringed direct image preserves injective objects. -/
instance moduleDirectImage_preservesInjectiveObjects :
    (moduleDirectImage f Λ).PreservesInjectiveObjects :=
  ModuleCat.Sheaf.ConstantRing.moduleDirectImage_preservesInjectiveObjects.{
    u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
