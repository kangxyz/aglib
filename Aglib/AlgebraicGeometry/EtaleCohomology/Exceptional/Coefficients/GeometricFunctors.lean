/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ConstantRing
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Images
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
  ModuleCat.Sheaf.ConstantRing.constantRingMap (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- The ring map extends exactly the original constant-ring unit. -/
@[reassoc]
theorem constantRingUnit_comp_constantRingMap :
    constantRingUnit X Λ ≫ (constantRingMap f Λ).hom =
      Functor.whiskerLeft (siteBaseChange f).op (constantRingUnit S Λ) :=
  ModuleCat.Sheaf.ConstantRing.constantRingUnit_comp_constantRingMap (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- Sectionwise normalization of the original constant-ring map. -/
@[reassoc]
theorem constantRingUnit_comp_constantRingMap_app (U : X.Etaleᵒᵖ) :
    (constantRingUnit X Λ).app U ≫ (constantRingMap f Λ).hom.app U =
      (constantRingUnit S Λ).app ((siteBaseChange f).op.obj U) :=
  ModuleCat.Sheaf.ConstantRing.constantRingUnit_comp_constantRingMap_app (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ U

/-- The genuine native direct image over the original constant-ring map. -/
def moduleDirectImage : ModuleSheaf S Λ ⥤ ModuleSheaf X Λ :=
  ModuleCat.Sheaf.ConstantRing.moduleDirectImage.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- The genuine direct image retains the original abelian direct image. -/
def moduleDirectImageUnderlyingIso :
    moduleDirectImage f Λ ⋙ SheafOfModules.toSheaf (constantRing X Λ) ≅
      SheafOfModules.toSheaf (constantRing S Λ) ⋙ directImage f :=
  ModuleCat.Sheaf.ConstantRing.moduleDirectImageUnderlyingIso.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- Direct image on module-valued sheaves on the same actual sites. -/
def moduleValuedDirectImage : ModuleValuedSheaf S Λ ⥤ ModuleValuedSheaf X Λ :=
  ModuleCat.Sheaf.ConstantRing.moduleValuedDirectImage.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- The shared ring morphism has the original sheafification-lift value. -/
theorem constantRingMap_eq_original : constantRingMap f Λ =
    ⟨CategoryTheory.sheafifyLift (Scheme.smallEtaleTopology X)
      (Functor.whiskerLeft (siteBaseChange f).op (constantRingUnit S Λ))
      (((siteBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)).obj
          (constantRing S Λ)).property⟩ := rfl

/-- The thin direct-image realization is the original native ringed pushforward. -/
theorem moduleDirectImage_eq_original :
    moduleDirectImage f Λ = SheafOfModules.pushforward (constantRingMap f Λ) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
