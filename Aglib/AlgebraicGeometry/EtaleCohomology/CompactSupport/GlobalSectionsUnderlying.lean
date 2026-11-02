/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.GlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying

/-! # The actual additive group underlying module global sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- The existing constant/sections adjunction transported by the original equivalence. -/
def moduleGlobalSectionsAdjunction :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (moduleSheafEquivalence X Λ).functor ⊣ moduleGlobalSections X Λ :=
  (Constructible.Modules.moduleConstantAdjunction Λ X).comp
    (moduleSheafEquivalence X Λ).toAdjunction

instance moduleGlobalSections_isRightAdjoint : (moduleGlobalSections X Λ).IsRightAdjoint :=
  (moduleGlobalSectionsAdjunction X Λ).isRightAdjoint

instance moduleGlobalSections_preservesLimits : PreservesLimits (moduleGlobalSections X Λ) :=
  inferInstance

/-- The original additive forgetting comparison evaluated at the actual terminal object. -/
def moduleGlobalSectionsUnderlyingIso :
    moduleGlobalSections X Λ ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      SheafOfModules.toSheaf (constantRing X Λ) ⋙ globalSections X :=
  Functor.isoWhiskerRight (moduleSheafInverseUnderlyingIso X Λ) (globalSections X)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
