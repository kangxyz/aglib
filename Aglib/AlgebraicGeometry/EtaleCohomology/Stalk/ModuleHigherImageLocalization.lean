/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ObjectProperty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleShortExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ModuleHigherImageComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.CategoryTheory.Abelian.ObjectProperty.ExactInverseImage

/-! # Native higher-image gluing through the original localization sequence

Both directions needed by support induction use the original lower-shriek
counit and closed inverse-image unit. The closed term is identified by the
actual finite direct-image composition, not by a replacement cohomology model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {U Z X S : Scheme.{u}} (f : X ⟶ S)
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hc : Set.range j = (Set.range i)ᶜ)
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

include hc

/-- The original localization sequence glues constructibility from the actual
open-extension term and the actual closed restriction. -/
theorem moduleNativeHigherDirectImage_isConstructible_of_localization
    (M : ModuleSheaf X Λ)
    (hU : ∀ q : ℕ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj
          ((moduleLowerShriek j Λ).obj ((moduleInverseImage j Λ).obj M)))))
    (hZ : ∀ q : ℕ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage (i ≫ f) Λ).rightDerived q).obj
          ((moduleInverseImage i Λ).obj M)))) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj M)) := by
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let P : ObjectProperty (ModuleSheaf S Λ) := ObjectProperty.inverseImage
    (Constructible.Modules.IsConstructible : ObjectProperty (ModuleValuedSheaf S Λ))
    (moduleSheafEquivalence S Λ).inverse
  apply (moduleDirectImage f Λ).rightDerived_property_of_shortExact P
    (moduleLocalizationShortComplex j Λ i hc M)
    (moduleLocalization_shortExact j Λ i hc M) hU ?_ q
  intro k
  exact P.prop_of_iso ((finiteModuleHigherDirectImageCompIso f i Λ k).app
    ((moduleInverseImage i Λ).obj M)) (hZ k)

/-- Conversely, the original open-extension term is constructible when the
whole coefficient and its closed restriction have constructible higher images.
This is the direction needed when compactifying a constant coefficient. -/
theorem moduleLowerShriekNativeHigherDirectImage_isConstructible_of_localization
    (M : ModuleSheaf X Λ)
    (hX : ∀ q : ℕ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj M)))
    (hZ : ∀ q : ℕ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage (i ≫ f) Λ).rightDerived q).obj
          ((moduleInverseImage i Λ).obj M)))) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj
          ((moduleLowerShriek j Λ).obj ((moduleInverseImage j Λ).obj M)))) := by
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let P : ObjectProperty (ModuleSheaf S Λ) := ObjectProperty.inverseImage
    (Constructible.Modules.IsConstructible : ObjectProperty (ModuleValuedSheaf S Λ))
    (moduleSheafEquivalence S Λ).inverse
  apply (moduleDirectImage f Λ).rightDerived_property_left_of_shortExact P
    (moduleLocalizationShortComplex j Λ i hc M)
    (moduleLocalization_shortExact j Λ i hc M) hX ?_ q
  intro k
  exact P.prop_of_iso ((finiteModuleHigherDirectImageCompIso f i Λ k).app
    ((moduleInverseImage i Λ).obj M)) (hZ k)

end AlgebraicGeometry.Scheme.EtaleCohomology
