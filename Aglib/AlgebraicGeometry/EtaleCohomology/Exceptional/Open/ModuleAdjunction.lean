/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.EtaleRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceTopology
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Adjunction
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exact extension by zero for genuine constant-ring modules

The coproduct extension on the actual small étale slice is formed with
arbitrary module coefficients, then transported through the proved native
constant-ring equivalences. Its right adjoint is the genuine ringed inverse
image, not a new functor supplied by an assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  (Λ : Type (u + 1)) [Ring Λ]

attribute [local instance] hasSheafifyModules

/-- The actual dense slice equivalence with arbitrary module coefficients. -/
def moduleEtaleSliceSheafEquivalence :
    ModuleValuedSheaf U Λ ≌
      Sheaf ((Scheme.smallEtaleTopology X).over (Scheme.Etale.mk j)) (ModuleCat.{u + 1} Λ) := by
  let : (etaleSliceEquivalence (Scheme.Etale.mk j)).inverse.IsDenseSubsite
      (Scheme.smallEtaleTopology (Scheme.Etale.mk j).left)
      ((Scheme.smallEtaleTopology X).over (Scheme.Etale.mk j)) :=
    etaleSliceBackward_isDenseSubsite (Scheme.Etale.mk j)
  exact ((etaleSliceEquivalence (Scheme.Etale.mk j)).sheafCongr
    ((Scheme.smallEtaleTopology X).over (Scheme.Etale.mk j))
    (Scheme.smallEtaleTopology (Scheme.Etale.mk j).left) (ModuleCat.{u + 1} Λ)).symm

/-- Lower shriek on module-valued sheaves is the actual slice coproduct extension. -/
def moduleValuedLowerShriek : ModuleValuedSheaf U Λ ⥤ ModuleValuedSheaf X Λ :=
  (moduleEtaleSliceSheafEquivalence j Λ).functor ⋙
    Sheaf.SliceCohomology.lowerShriek (Scheme.smallEtaleTopology X)
      (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j)

/-- Slice restriction is literal module-valued chart restriction. -/
def moduleEtaleSliceRestrictionIso :
    (Scheme.smallEtaleTopology X).overPullback (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j) ⋙
        (moduleEtaleSliceSheafEquivalence j Λ).inverse ≅ moduleValuedEtaleRestriction j Λ :=
  Iso.refl _

/-- The slice adjunction retains literal module-valued restriction. -/
def moduleValuedLowerShriekRestrictionAdjunction :
    moduleValuedLowerShriek j Λ ⊣ moduleValuedEtaleRestriction j Λ :=
  ((moduleEtaleSliceSheafEquivalence j Λ).toAdjunction.comp
    (Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
      (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j))).ofNatIsoRight
        (moduleEtaleSliceRestrictionIso j Λ)

/-- Module-valued lower shriek is left adjoint to the original site inverse image. -/
def moduleValuedLowerShriekAdjunction :
    moduleValuedLowerShriek j Λ ⊣ moduleValuedInverseImage j Λ :=
  (moduleValuedLowerShriekRestrictionAdjunction j Λ).ofNatIsoRight
    (moduleValuedInverseImageEtaleIso j Λ).symm

instance moduleValuedLowerShriek_preservesFiniteLimits :
    PreservesFiniteLimits (moduleValuedLowerShriek j Λ) := by
  let E := moduleEtaleSliceSheafEquivalence j Λ
  let : PreservesLimitsOfSize.{0, 0} E.functor :=
    E.symm.toAdjunction.rightAdjoint_preservesLimits
  let : PreservesFiniteLimits E.functor :=
    PreservesLimitsOfSize0.preservesFiniteLimits _
  let : AB4OfSize.{u} (ModuleCat.{u + 1} Λ) := AB4OfSize_shrink.{u, u + 1} _
  let : PreservesFiniteLimits (Sheaf.SliceCohomology.lowerShriek
      (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j)) :=
    Sheaf.SliceCohomology.lowerShriek_preservesFiniteLimits
      (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j)
  exact comp_preservesFiniteLimits E.functor _

/-- Genuine native constant-ring module extension by zero. -/
def moduleLowerShriek : ModuleSheaf U Λ ⥤ ModuleSheaf X Λ :=
  ((moduleSheafEquivalence U Λ).inverse ⋙ moduleValuedLowerShriek j Λ) ⋙
    (moduleSheafEquivalence X Λ).functor

/-- The transported adjunction before identifying its native right adjoint. -/
def moduleLowerShriekTransportAdjunction :
    moduleLowerShriek j Λ ⊣
      (moduleSheafEquivalence X Λ).inverse ⋙
        moduleValuedInverseImage j Λ ⋙ (moduleSheafEquivalence U Λ).functor :=
  (((moduleSheafEquivalence U Λ).symm.toAdjunction.comp
    (moduleValuedLowerShriekAdjunction j Λ)).comp
      (moduleSheafEquivalence X Λ).toAdjunction)

/-- The right-adjoint identification uses the proved original native pullback comparison. -/
def moduleLowerShriekRightIso :
    (moduleSheafEquivalence X Λ).inverse ⋙
        moduleValuedInverseImage j Λ ⋙ (moduleSheafEquivalence U Λ).functor ≅
      moduleInverseImage j Λ :=
  (Functor.associator _ _ _).symm ≪≫ (moduleInverseImageTransportIso j Λ).symm

/-- The actual module lower-shriek/native inverse-image adjunction. -/
def moduleLowerShriekAdjunction : moduleLowerShriek j Λ ⊣ moduleInverseImage j Λ :=
  (moduleLowerShriekTransportAdjunction j Λ).ofNatIsoRight (moduleLowerShriekRightIso j Λ)

instance moduleLowerShriek_isLeftAdjoint : (moduleLowerShriek j Λ).IsLeftAdjoint :=
  (moduleLowerShriekAdjunction j Λ).isLeftAdjoint

instance moduleLowerShriek_preservesFiniteLimits :
    PreservesFiniteLimits (moduleLowerShriek j Λ) := by
  let EU := moduleSheafEquivalence U Λ
  let EX := moduleSheafEquivalence X Λ
  let : PreservesLimitsOfSize.{0, 0} EU.inverse := EU.toAdjunction.rightAdjoint_preservesLimits
  let : PreservesFiniteLimits EU.inverse := PreservesLimitsOfSize0.preservesFiniteLimits _
  let : PreservesLimitsOfSize.{0, 0} EX.functor :=
    EX.symm.toAdjunction.rightAdjoint_preservesLimits
  let : PreservesFiniteLimits EX.functor := PreservesLimitsOfSize0.preservesFiniteLimits _
  exact comp_preservesFiniteLimits (EU.inverse ⋙ moduleValuedLowerShriek j Λ) EX.functor

instance moduleLowerShriek_preservesColimits : PreservesColimits (moduleLowerShriek j Λ) := by
  infer_instance

instance moduleLowerShriek_additive : (moduleLowerShriek j Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Exactness of the genuine native module extension by zero. -/
theorem shortExact_moduleLowerShriek {S : ShortComplex (ModuleSheaf U Λ)}
    (hS : S.ShortExact) : (S.map (moduleLowerShriek j Λ)).ShortExact :=
  hS.map_of_exact (moduleLowerShriek j Λ)

/-- The actual adjunction unit is the transported unit followed by the native comparison. -/
theorem moduleLowerShriekAdjunction_unit (M : ModuleSheaf U Λ) :
    (moduleLowerShriekAdjunction j Λ).unit.app M =
      (moduleLowerShriekTransportAdjunction j Λ).unit.app M ≫
        (moduleLowerShriekRightIso j Λ).hom.app ((moduleLowerShriek j Λ).obj M) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
