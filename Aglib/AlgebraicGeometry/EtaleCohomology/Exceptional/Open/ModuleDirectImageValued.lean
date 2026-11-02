/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangeMate
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ValuedComparison

/-! # Original direct-image composition under the coefficient equivalence -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients
open CategoryTheory.TorsionZMod.Ringed

attribute [local instance] hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard hasSheafifyModules

variable {X S T : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
  (f : S ⟶ X) (g : T ⟶ S)

/-- Whole original valued comparison of native direct-image composition. -/
theorem moduleDirectImageCompIso_hom_valued_whole :
    Functor.whiskerRight (moduleDirectImageCompIso Λ f g).hom
        (moduleSheafEquivalence X Λ).inverse ≫ (moduleDirectImageCompRightIso Λ f g).hom =
      (moduleDirectImageComparison (g ≫ f) Λ).hom ≫
        Functor.whiskerLeft (moduleSheafEquivalence T Λ).inverse
          (moduleValuedDirectImageCompIso Λ f g).hom :=
  ValuedComparison.hom_comparison_of_whisker (moduleSheafEquivalence X Λ).inverse
    (moduleDirectImageCompIso Λ f g) (moduleDirectImageComparison (g ≫ f) Λ)
    (moduleDirectImageCompRightIso Λ f g) (moduleValuedDirectImageCompIso Λ f g)
    (ModuleCat.Sheaf.ConstantRing.moduleDirectImageCompIso_whisker.{
      u + 1, u, u + 1, u, u + 1, u, u + 1, u + 1}
      (siteBaseChange f) (siteBaseChange g) (siteBaseChange (g ≫ f))
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
      (Scheme.smallEtaleTopology T) Λ (siteBaseChangeComp f g).symm)

/-- The native composition comparison is the original valued comparison after transport. -/
@[reassoc]
theorem moduleDirectImageCompIso_hom_valued (M : ModuleSheaf T Λ) :
    (moduleSheafEquivalence X Λ).inverse.map
        ((moduleDirectImageCompIso Λ f g).hom.app M) ≫
      (moduleDirectImageCompRightIso Λ f g).hom.app M =
    (moduleDirectImageComparison (g ≫ f) Λ).hom.app M ≫
      (moduleValuedDirectImageCompIso Λ f g).hom.app
        ((moduleSheafEquivalence T Λ).inverse.obj M) := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    NatTrans.congr_app (moduleDirectImageCompIso_hom_valued_whole Λ f g) M

end AlgebraicGeometry.Scheme.EtaleCohomology
