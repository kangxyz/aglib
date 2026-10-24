/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleSliceUnderlying
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Coefficients

/-! # Genuine module extension by zero has the original abelian underlying extension -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  (Λ : Type (u + 1)) [Ring Λ]

attribute [local instance] hasSheafifyLarge hasSheafifyModules moduleForget_preservesSheafification

/-- The original module-valued lower shriek commutes with additive forgetting. -/
def moduleValuedLowerShriekUnderlyingIso :
    moduleValuedLowerShriek j Λ ⋙
      sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
    sheafCompose (Scheme.smallEtaleTopology U)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ etaleLowerShriek j :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Sheaf.SliceCohomology.lowerShriekCoefficientIso
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
        (Scheme.Etale.mk j) (Scheme.smallEtaleTopology X)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleEtaleSliceUnderlyingIso j Λ) _ ≪≫
    Functor.associator _ _ _

/-- The native constant-ring extension has the actual abelian extension underneath. -/
def moduleLowerShriekUnderlyingIso :
    moduleLowerShriek j Λ ⋙ SheafOfModules.toSheaf (constantRing X Λ) ≅
      SheafOfModules.toSheaf (constantRing U Λ) ⋙ etaleLowerShriek j :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleSheafUnderlyingIso X Λ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleValuedLowerShriekUnderlyingIso j Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafInverseUnderlyingIso U Λ) _

end AlgebraicGeometry.Scheme.EtaleCohomology
