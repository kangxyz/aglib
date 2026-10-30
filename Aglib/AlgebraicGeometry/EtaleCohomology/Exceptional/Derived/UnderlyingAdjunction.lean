/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Underlying
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.NativeAdjunctionUnderlying
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.UnderlyingMate

/-!
# The original module-derived adjunction under scalar forgetting

The fixed inverse-image comparison and the acyclicity-based direct-image comparison
are mates under the original derived adjunctions. Their identification uses the
original complex-unit equations, cancelling only exact scalar-forgetting units.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

local instance underlyingMateDirectSourceComparisonIsIso :
    IsIso (rightDerivedFunctorPlusCompComparison
      (moduleDirectImage f Λ) (SheafOfModules.toSheaf (constantRing S Λ))) :=
  isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology _ _

local instance underlyingMateDirectTargetComparisonIsIso :
    IsIso (rightDerivedFunctorPlusCompComparison
      (SheafOfModules.toSheaf (constantRing X Λ)) (directImage f)) :=
  isIso_rightDerivedFunctorPlusCompComparison_of_acyclic _ _
    (fun I _ n => higherDirectImage_moduleInjective_isZero f Λ I n)

/-- The inverse scalar comparison retains the original exact complex square. -/
theorem moduleDerivedInverseImageUnderlyingIso_exactComparison
    (K : CochainComplex.Plus (ModuleSheaf S Λ)) :
    ExactComparisonSquareEquation (moduleInverseImage f Λ)
      (SheafOfModules.toSheaf (constantRing X Λ))
      (SheafOfModules.toSheaf (constantRing S Λ)) (inverseImage f)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso Λ f).inv)
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageUnderlyingIso Λ f).inv) K :=
  threeFactorInverse_exactComparison
    (SheafOfModules.toSheaf (constantRing S Λ))
    (SheafOfModules.toSheaf (constantRing X Λ))
    (moduleInverseImage f Λ) (inverseImage f) (moduleInverseImageUnderlyingIso Λ f) K

/-- The fixed direct-image comparison satisfies the normalized original-unit equation. -/
theorem moduleDerivedDirectImageUnderlyingIso_originalUnit
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleDerivedUnderlying Λ S).map
        ((moduleDirectImage f Λ).rightDerivedFunctorPlusUnit.app K) ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      (derivedDirectImage f).map
        ((SheafOfModules.toSheaf (constantRing X Λ)).rightDerivedFunctorPlusExactComparison.hom.app
          K) =
    (SheafOfModules.toSheaf (constantRing S Λ)).rightDerivedFunctorPlusExactComparison.hom.app
        ((moduleDirectImage f Λ).mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (moduleDirectImageUnderlyingIso f Λ)).hom.app K) ≫
      (directImage f).rightDerivedFunctorPlusUnit.app
        ((SheafOfModules.toSheaf (constantRing X Λ)).mapCochainComplexPlus.obj K) :=
  threeFactorComparison_originalUnit
    (SheafOfModules.toSheaf (constantRing S Λ))
    (SheafOfModules.toSheaf (constantRing X Λ))
    (moduleDirectImage f Λ) (directImage f) (moduleDirectImageUnderlyingIso f Λ) K

/-- The original derived direct-image comparison is the mate of the fixed inverse
scalar comparison, rather than a separately chosen isomorphism. -/
theorem mate_moduleDerivedInverseImageUnderlyingIso_inv :
    (mateEquiv (moduleDerivedAdjunction Λ f) (derivedImageAdjunction f)
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageUnderlyingIso Λ f).inv)).natTrans =
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom :=
  mate_threeFactorInverse_eq_threeFactorDirect
    (SheafOfModules.toSheaf (constantRing S Λ))
    (SheafOfModules.toSheaf (constantRing X Λ))
    (moduleInverseImage f Λ) (inverseImage f) (moduleDirectImage f Λ) (directImage f)
    (moduleInverseImageAdjunction f Λ) (inverseImageAdjunction f)
    (moduleInverseImageUnderlyingIso Λ f) (moduleDirectImageUnderlyingIso f Λ)
    (mate_moduleInverseImageUnderlyingIso_inv (Λ := Λ) (f := f))

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
