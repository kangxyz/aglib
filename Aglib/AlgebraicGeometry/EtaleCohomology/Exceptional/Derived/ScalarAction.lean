/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Underlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarAction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Comparison.Equivariance

/-! # Genuine Ring equivariance of the original derived underlying comparison

The original constant-ring unit proves the ordinary coefficient square. The
canonical derived composition comparisons then carry that square to the
existing relative-acyclicity comparison, with all four realization universes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
universe u wMX wMS wAX wAS
attribute [local instance] hasSheafifyLarge
variable (Λ : Type (u + 1)) [Ring Λ] {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

local instance scalarDirectImageSourceComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison
      (moduleDirectImage f Λ) (SheafOfModules.toSheaf (constantRing S Λ))) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology _ _

local instance scalarDirectImageTargetComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison
      (SheafOfModules.toSheaf (constantRing X Λ)) (directImage f)) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_acyclic _ _
    (fun I _ n => higherDirectImage_moduleInjective_isZero f Λ I n)

/-- The original derived direct-image comparison intertwines every actual left scalar. -/
theorem moduleDerivedDirectImageUnderlyingIso_scalar (a : Λ) :
    Functor.whiskerLeft (moduleDerivedDirectImage Λ f)
        ((SheafOfModules.toSheaf (constantRing S Λ)).rightDerivedFunctorPlusNatTrans
          (moduleUnderlyingScalar Λ S a)) ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom =
    (moduleDerivedDirectImageUnderlyingIso Λ f).hom ≫
      Functor.whiskerRight
        ((SheafOfModules.toSheaf (constantRing X Λ)).rightDerivedFunctorPlusNatTrans
          (moduleUnderlyingScalar Λ X a)) (derivedDirectImage f) :=
  Functor.rightDerivedFunctorPlusThreeFactorIso_equivariant
    (moduleDirectImage f Λ) (SheafOfModules.toSheaf (constantRing S Λ))
    (SheafOfModules.toSheaf (constantRing X Λ)) (directImage f)
    (moduleDirectImageUnderlyingIso f Λ) (moduleUnderlyingScalar Λ S a)
    (moduleUnderlyingScalar Λ X a) (moduleDirectImageUnderlyingIso_scalar Λ f a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
