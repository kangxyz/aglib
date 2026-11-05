/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.RingedScalarAction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.GeometricFunctors

/-! # Original noncentral scalar actions and genuine module direct image -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
universe u
attribute [local instance] CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Noncentral scalars act on the original underlying abelian sheaf, not as module maps. -/
abbrev moduleUnderlyingScalar (X : Scheme.{u}) (a : Λ) :
    SheafOfModules.toSheaf (constantRing X Λ) ⟶
      SheafOfModules.toSheaf (constantRing X Λ) :=
  SheafOfModules.underlyingScalarSection (constantRing X Λ) (constantRingUnit X Λ) a

/-- The actual constant-ring unit law supplies the original direct-image scalar square. -/
theorem moduleDirectImageUnderlyingIso_scalar {X S : Scheme.{u}} (f : X ⟶ S) (a : Λ) :
    Functor.whiskerLeft (moduleDirectImage f Λ) (moduleUnderlyingScalar Λ S a) ≫
        (moduleDirectImageUnderlyingIso f Λ).hom =
      (moduleDirectImageUnderlyingIso f Λ).hom ≫
        Functor.whiskerRight (moduleUnderlyingScalar Λ X a) (directImage f) := by
  ext M U x
  let y : M.val.obj ((siteBaseChange f).op.obj U) := x
  change ((constantRingMap f Λ).hom.app U ((constantRingUnit S Λ).app U a) :
      (constantRing X Λ).obj.obj ((siteBaseChange f).op.obj U)) • y =
    (constantRingUnit X Λ).app ((siteBaseChange f).op.obj U) a • y
  exact congrArg (fun r : (constantRing X Λ).obj.obj ((siteBaseChange f).op.obj U) => r • y)
    (ConcreteCategory.congr_hom (constantRingUnit_comp_constantRingMap_app f Λ U) a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
