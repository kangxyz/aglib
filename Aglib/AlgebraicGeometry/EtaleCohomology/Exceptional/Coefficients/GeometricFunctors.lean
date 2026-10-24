/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ConstantRing
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Native direct image for arbitrary constant-ring modules

The ring map is the unique extension of the original constant-ring unit on
the source. The functor is the native `SheafOfModules.pushforward`, not a
transported replacement. Its underlying abelian functor is the original
small-étale direct image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.TorsionZMod.Ringed

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} (f : S ⟶ X) (Λ : Type (u + 1)) [Ring Λ]

/-- The constant ring map along the actual continuous small-étale base-change functor. -/
def constantRingMap : constantRing X Λ ⟶
    ((siteBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)).obj (constantRing S Λ) :=
  ⟨CategoryTheory.sheafifyLift (Scheme.smallEtaleTopology X)
    (Functor.whiskerLeft (siteBaseChange f).op (constantRingUnit S Λ))
    (((siteBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)).obj
        (constantRing S Λ)).property⟩

/-- The ring map extends exactly the original constant-ring unit. -/
@[reassoc]
theorem constantRingUnit_comp_constantRingMap :
    constantRingUnit X Λ ≫ (constantRingMap f Λ).hom =
      Functor.whiskerLeft (siteBaseChange f).op (constantRingUnit S Λ) :=
  CategoryTheory.toSheafify_sheafifyLift _ _ _

/-- Sectionwise normalization of the original constant-ring map. -/
@[reassoc]
theorem constantRingUnit_comp_constantRingMap_app (U : X.Etaleᵒᵖ) :
    (constantRingUnit X Λ).app U ≫ (constantRingMap f Λ).hom.app U =
      (constantRingUnit S Λ).app ((siteBaseChange f).op.obj U) :=
  congrArg (fun α => α.app U) (constantRingUnit_comp_constantRingMap f Λ)

/-- The genuine native direct image over the original constant-ring map. -/
def moduleDirectImage : ModuleSheaf S Λ ⥤ ModuleSheaf X Λ :=
  SheafOfModules.pushforward (constantRingMap f Λ)

/-- The genuine direct image retains the original abelian direct image. -/
def moduleDirectImageUnderlyingIso :
    moduleDirectImage f Λ ⋙ SheafOfModules.toSheaf (constantRing X Λ) ≅
      SheafOfModules.toSheaf (constantRing S Λ) ⋙ directImage f :=
  Iso.refl _

/-- Direct image on module-valued sheaves on the same actual sites. -/
def moduleValuedDirectImage : ModuleValuedSheaf S Λ ⥤ ModuleValuedSheaf X Λ :=
  (siteBaseChange f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
