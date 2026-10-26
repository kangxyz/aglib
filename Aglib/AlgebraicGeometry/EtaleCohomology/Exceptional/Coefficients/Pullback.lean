/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.GeometricFunctors
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Pullback
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# The native constant-ring pullback and its original unit

Right-adjoint existence is proved for the genuine ringed direct image through
its sectionwise comparison with module-valued sheaves. This does not use a
small-category replacement for the actual étale site. Pullback is then the
native `SheafOfModules.pullback`; its comparison with the transported site
pullback is normalized by the original adjunction unit.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits
open CategoryTheory.TorsionZMod.Ringed

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} (f : S ⟶ X) (Λ : Type (u + 1)) [Ring Λ]

/-- On sections the direct-image bridge is the original scalar-restriction composition. -/
def moduleDirectImageComparisonComponent (M : ModuleSheaf S Λ) (U : X.Etaleᵒᵖ) :
    (((moduleSheafEquivalence X Λ).inverse.obj
      ((moduleDirectImage f Λ).obj M)).obj.obj U) ≅
    (((moduleValuedDirectImage f Λ).obj
      ((moduleSheafEquivalence S Λ).inverse.obj M)).obj.obj U) :=
  ModuleCat.Sheaf.ConstantRing.moduleDirectImageComparisonComponent.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ M U

/-- The inverse constant-ring equivalence commutes with the actual native direct image. -/
def moduleDirectImageComparison :
    moduleDirectImage f Λ ⋙ (moduleSheafEquivalence X Λ).inverse ≅
      (moduleSheafEquivalence S Λ).inverse ⋙ moduleValuedDirectImage f Λ :=
  ModuleCat.Sheaf.ConstantRing.moduleDirectImageComparison.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- Comparison of the native direct image with the equivalent module-valued construction. -/
def moduleDirectImageTransportIso : moduleDirectImage f Λ ≅
    (moduleSheafEquivalence S Λ).inverse ⋙ moduleValuedDirectImage f Λ ⋙
      (moduleSheafEquivalence X Λ).functor :=
  ModuleCat.Sheaf.ConstantRing.moduleDirectImageTransportIso.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- Native sheafification for module coefficients at the actual site size. -/
theorem hasSheafifyModules (X : Scheme.{u}) :
    HasSheafify (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ) := by
  infer_instance

attribute [local instance] hasSheafifyModules

/-- The original continuous-site pullback for module-valued sheaves. -/
def moduleValuedInverseImage : ModuleValuedSheaf X Λ ⥤ ModuleValuedSheaf S Λ :=
  ModuleCat.Sheaf.ConstantRing.moduleValuedInverseImage.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- The original module-valued continuous-site adjunction. -/
def moduleValuedInverseImageAdjunction :
    moduleValuedInverseImage f Λ ⊣ moduleValuedDirectImage f Λ :=
  ModuleCat.Sheaf.ConstantRing.moduleValuedInverseImageAdjunction.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- Transport supplies a left adjoint to the genuine native ringed direct image. -/
def moduleTransportAdjunction :
    ((moduleSheafEquivalence X Λ).inverse ⋙ moduleValuedInverseImage f Λ) ⋙
      (moduleSheafEquivalence S Λ).functor ⊣ moduleDirectImage f Λ :=
  ModuleCat.Sheaf.ConstantRing.moduleTransportAdjunction.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

instance moduleDirectImage_isRightAdjoint : (moduleDirectImage f Λ).IsRightAdjoint :=
  ModuleCat.Sheaf.ConstantRing.moduleDirectImage_isRightAdjoint.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- The same actual adjoint witness at the literal native pushforward presentation. -/
local instance nativeConstantRingPushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{u + 1} (constantRingMap f Λ)).IsRightAdjoint :=
  moduleDirectImage_isRightAdjoint f Λ

/-- Genuine native pullback along the original morphism of constant ring sheaves. -/
def moduleInverseImage : ModuleSheaf X Λ ⥤ ModuleSheaf S Λ :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImage.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- The original native ringed pullback/direct-image adjunction. -/
def moduleInverseImageAdjunction : moduleInverseImage f Λ ⊣ moduleDirectImage f Λ :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImageAdjunction.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- Native pullback agrees with the transported original continuous-site pullback. -/
def moduleInverseImageTransportIso : moduleInverseImage f Λ ≅
    ((moduleSheafEquivalence X Λ).inverse ⋙ moduleValuedInverseImage f Λ) ⋙
      (moduleSheafEquivalence S Λ).functor :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImageTransportIso.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- The pullback comparison preserves the original native adjunction unit. -/
@[reassoc]
theorem moduleInverseImageTransportIso_unit (M : ModuleSheaf X Λ) :
    (moduleInverseImageAdjunction f Λ).unit.app M ≫
      (moduleDirectImage f Λ).map ((moduleInverseImageTransportIso f Λ).hom.app M) =
    (moduleTransportAdjunction f Λ).unit.app M :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImageTransportIso_unit_app.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ M

/-- The shared native inverse image retains the original ringed pullback value. -/
theorem moduleInverseImage_eq_original :
    moduleInverseImage f Λ = SheafOfModules.pullback.{u + 1} (constantRingMap f Λ) := rfl

/-- The shared transport isomorphism retains the original left-adjoint uniqueness value. -/
theorem moduleInverseImageTransportIso_eq_original : moduleInverseImageTransportIso f Λ =
    (moduleInverseImageAdjunction f Λ).leftAdjointUniq (moduleTransportAdjunction f Λ) := rfl

/-- The whole actual inverse-image comparison preserves the native unit. -/
theorem moduleInverseImageTransportIso_unit_whole :
    (moduleInverseImageAdjunction f Λ).unit ≫
        Functor.whiskerRight (moduleInverseImageTransportIso f Λ).hom (moduleDirectImage f Λ) =
      (moduleTransportAdjunction f Λ).unit :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImageTransportIso_unit.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

/-- The whole actual inverse-image comparison preserves the native counit. -/
theorem moduleInverseImageTransportIso_counit_whole :
    Functor.whiskerLeft (moduleDirectImage f Λ) (moduleInverseImageTransportIso f Λ).hom ≫
      (moduleTransportAdjunction f Λ).counit = (moduleInverseImageAdjunction f Λ).counit :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImageTransportIso_counit.{
    u + 1, u, u + 1, u, u + 1, u + 1} (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
