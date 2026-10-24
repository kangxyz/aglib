/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.GeometricFunctors
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

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

variable {X S : Scheme.{u}} (f : S ⟶ X) (Λ : Type (u + 1)) [Ring Λ]

/-- On sections the direct-image bridge is the original scalar-restriction composition. -/
def moduleDirectImageComparisonComponent (M : ModuleSheaf S Λ) (U : X.Etaleᵒᵖ) :
    (((moduleSheafEquivalence X Λ).inverse.obj
      ((moduleDirectImage f Λ).obj M)).obj.obj U) ≅
    (((moduleValuedDirectImage f Λ).obj
      ((moduleSheafEquivalence S Λ).inverse.obj M)).obj.obj U) :=
  (ModuleCat.restrictScalarsComp'App
    ((constantRingUnit X Λ).app U).hom ((constantRingMap f Λ).hom.app U).hom
    ((constantRingUnit S Λ).app ((siteBaseChange f).op.obj U)).hom
    (congrArg RingCat.Hom.hom (constantRingUnit_comp_constantRingMap_app f Λ U).symm)
    (ModuleCat.of ((constantRing S Λ).obj.obj ((siteBaseChange f).op.obj U))
      (M.val.obj ((siteBaseChange f).op.obj U)))).symm

/-- The inverse constant-ring equivalence commutes with the actual native direct image. -/
def moduleDirectImageComparison :
    moduleDirectImage f Λ ⋙ (moduleSheafEquivalence X Λ).inverse ≅
      (moduleSheafEquivalence S Λ).inverse ⋙ moduleValuedDirectImage f Λ :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    (NatIso.ofComponents (moduleDirectImageComparisonComponent f Λ M)
      (by intros; ext x; rfl)))
    (by intros; apply ObjectProperty.hom_ext; ext U x; rfl)

/-- Comparison of the native direct image with the equivalent module-valued construction. -/
def moduleDirectImageTransportIso : moduleDirectImage f Λ ≅
    (moduleSheafEquivalence S Λ).inverse ⋙ moduleValuedDirectImage f Λ ⋙
      (moduleSheafEquivalence X Λ).functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (moduleSheafEquivalence X Λ).counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDirectImageComparison f Λ)
      (moduleSheafEquivalence X Λ).functor ≪≫
    Functor.associator _ _ _

/-- Native sheafification for module coefficients at the actual site size. -/
theorem hasSheafifyModules (X : Scheme.{u}) :
    HasSheafify (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ) := by
  infer_instance

attribute [local instance] hasSheafifyModules

/-- The original continuous-site pullback for module-valued sheaves. -/
def moduleValuedInverseImage : ModuleValuedSheaf X Λ ⥤ ModuleValuedSheaf S Λ :=
  (siteBaseChange f).sheafPullback (ModuleCat.{u + 1} Λ)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)

/-- The original module-valued continuous-site adjunction. -/
def moduleValuedInverseImageAdjunction :
    moduleValuedInverseImage f Λ ⊣ moduleValuedDirectImage f Λ :=
  (siteBaseChange f).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)

/-- Transport supplies a left adjoint to the genuine native ringed direct image. -/
def moduleTransportAdjunction :
    ((moduleSheafEquivalence X Λ).inverse ⋙ moduleValuedInverseImage f Λ) ⋙
      (moduleSheafEquivalence S Λ).functor ⊣ moduleDirectImage f Λ :=
  (((moduleSheafEquivalence X Λ).symm.toAdjunction.comp
    (moduleValuedInverseImageAdjunction f Λ)).comp
      (moduleSheafEquivalence S Λ).toAdjunction).ofNatIsoRight
        (moduleDirectImageTransportIso f Λ).symm

instance moduleDirectImage_isRightAdjoint : (moduleDirectImage f Λ).IsRightAdjoint :=
  (moduleTransportAdjunction f Λ).isRightAdjoint

/-- Genuine native pullback along the original morphism of constant ring sheaves. -/
def moduleInverseImage : ModuleSheaf X Λ ⥤ ModuleSheaf S Λ := by
  let : (SheafOfModules.pushforward (constantRingMap f Λ)).IsRightAdjoint :=
    moduleDirectImage_isRightAdjoint f Λ
  exact SheafOfModules.pullback (constantRingMap f Λ)

/-- The original native ringed pullback/direct-image adjunction. -/
def moduleInverseImageAdjunction : moduleInverseImage f Λ ⊣ moduleDirectImage f Λ := by
  let : (SheafOfModules.pushforward (constantRingMap f Λ)).IsRightAdjoint :=
    moduleDirectImage_isRightAdjoint f Λ
  exact SheafOfModules.pullbackPushforwardAdjunction (constantRingMap f Λ)

/-- Native pullback agrees with the transported original continuous-site pullback. -/
def moduleInverseImageTransportIso : moduleInverseImage f Λ ≅
    ((moduleSheafEquivalence X Λ).inverse ⋙ moduleValuedInverseImage f Λ) ⋙
      (moduleSheafEquivalence S Λ).functor :=
  (moduleInverseImageAdjunction f Λ).leftAdjointUniq (moduleTransportAdjunction f Λ)

/-- The pullback comparison preserves the original native adjunction unit. -/
@[reassoc]
theorem moduleInverseImageTransportIso_unit (M : ModuleSheaf X Λ) :
    (moduleInverseImageAdjunction f Λ).unit.app M ≫
      (moduleDirectImage f Λ).map ((moduleInverseImageTransportIso f Λ).hom.app M) =
    (moduleTransportAdjunction f Λ).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
