/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingAcyclic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ClosedExactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.Adjunction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Comparison.ThreeFactor

/-!
# Original derived images under additive coefficient forgetting

The exact underlying-sheaf functor descends to the existing bounded-below derived
categories. Its direct-image comparison uses the proved relative acyclicity of
underlying genuine module injectives, not preservation of injectivity by scalar
forgetting. Both comparisons retain their original composite-unit equations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The installed derived functor of the original exact additive forgetting functor. -/
abbrev moduleDerivedUnderlying (X : Scheme.{u})
    [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)] :
    DerivedCategory.Plus (ModuleSheaf X Λ) ⥤
      DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X) :=
  (SheafOfModules.toSheaf (constantRing X Λ)).rightDerivedFunctorPlus

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

local instance inverseImageUnderlyingSourceComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison
      (moduleInverseImage f Λ) (SheafOfModules.toSheaf (constantRing X Λ))) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology _ _

local instance inverseImageUnderlyingTargetComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison
      (SheafOfModules.toSheaf (constantRing S Λ)) (inverseImage f)) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology _ _

local instance directImageUnderlyingSourceComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison
      (moduleDirectImage f Λ) (SheafOfModules.toSheaf (constantRing S Λ))) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology _ _

local instance directImageUnderlyingTargetComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison
      (SheafOfModules.toSheaf (constantRing X Λ)) (directImage f)) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_acyclic _ _
    (fun I _ n => higherDirectImage_moduleInjective_isZero f Λ I n)

/-- Exact scalar forgetting commutes with original derived inverse image. -/
def moduleDerivedInverseImageUnderlyingIso :
    moduleDerivedInverseImage Λ f ⋙ moduleDerivedUnderlying Λ X ≅
      moduleDerivedUnderlying Λ S ⋙ derivedInverseImage f :=
  Functor.rightDerivedFunctorPlusThreeFactorIso
    (moduleInverseImage f Λ) (SheafOfModules.toSheaf (constantRing X Λ))
    (SheafOfModules.toSheaf (constantRing S Λ)) (inverseImage f)
    (moduleInverseImageUnderlyingIso Λ f)

/-- The shared constructor gives the original inverse-image three-factor map. -/
theorem moduleDerivedInverseImageUnderlyingIso_eq_original :
    moduleDerivedInverseImageUnderlyingIso Λ f =
      (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
        (moduleInverseImage f Λ) (SheafOfModules.toSheaf (constantRing X Λ))).symm ≪≫
      Functor.rightDerivedFunctorPlusIso
        (moduleInverseImage f Λ ⋙ SheafOfModules.toSheaf (constantRing X Λ))
        (moduleInverseImageUnderlyingIso Λ f) ≪≫
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
        (SheafOfModules.toSheaf (constantRing S Λ)) (inverseImage f) := by
  rw [moduleDerivedInverseImageUnderlyingIso, Functor.rightDerivedFunctorPlusThreeFactorIso,
    Functor.rightDerivedFunctorPlusCompIso_eq_of_preservesHomology,
    Functor.rightDerivedFunctorPlusCompIso_eq_of_preservesHomology]

/-- The original module-derived direct image has the original abelian image underneath. -/
def moduleDerivedDirectImageUnderlyingIso :
    moduleDerivedDirectImage Λ f ⋙ moduleDerivedUnderlying Λ S ≅
      moduleDerivedUnderlying Λ X ⋙ derivedDirectImage f :=
  Functor.rightDerivedFunctorPlusThreeFactorIso
    (moduleDirectImage f Λ) (SheafOfModules.toSheaf (constantRing S Λ))
    (SheafOfModules.toSheaf (constantRing X Λ)) (directImage f)
    (moduleDirectImageUnderlyingIso f Λ)

/-- The shared constructor gives the original relative-acyclicity direct-image map. -/
theorem moduleDerivedDirectImageUnderlyingIso_eq_original :
    moduleDerivedDirectImageUnderlyingIso Λ f =
      (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
        (moduleDirectImage f Λ) (SheafOfModules.toSheaf (constantRing S Λ))).symm ≪≫
      (moduleDirectImage f Λ ⋙ SheafOfModules.toSheaf (constantRing S Λ)).rightDerivedFunctorPlusIso
        (moduleDirectImageUnderlyingIso f Λ) ≪≫
      Functor.rightDerivedFunctorPlusCompIsoOfAcyclic
        (SheafOfModules.toSheaf (constantRing X Λ)) (directImage f)
        (fun I _ n => higherDirectImage_moduleInjective_isZero f Λ I n) := by
  rw [moduleDerivedDirectImageUnderlyingIso, Functor.rightDerivedFunctorPlusThreeFactorIso,
    Functor.rightDerivedFunctorPlusCompIso_eq_of_preservesHomology,
    Functor.rightDerivedFunctorPlusCompIso_eq_of_acyclic _ _
      (fun I _ n => higherDirectImage_moduleInjective_isZero f Λ I n)]

/-- The inverse-image scalar comparison retains the two original composite units. -/
theorem moduleDerivedInverseImageUnderlyingIso_unit
    (K : CochainComplex.Plus (ModuleSheaf S Λ)) :
    (Functor.rightDerivedFunctorPlusCompUnit (moduleInverseImage f Λ)
        (SheafOfModules.toSheaf (constantRing X Λ))).app K ≫
      (moduleDerivedInverseImageUnderlyingIso Λ f).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (moduleInverseImageUnderlyingIso Λ f)).hom.app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit
        (SheafOfModules.toSheaf (constantRing S Λ)) (inverseImage f)).app K := by
  exact Functor.rightDerivedFunctorPlusThreeFactorIso_unit_app
    (moduleInverseImage f Λ) (SheafOfModules.toSheaf (constantRing X Λ))
    (SheafOfModules.toSheaf (constantRing S Λ)) (inverseImage f)
    (moduleInverseImageUnderlyingIso Λ f) K

/-- The direct-image scalar comparison retains the original acyclicity comparison unit. -/
theorem moduleDerivedDirectImageUnderlyingIso_unit
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (Functor.rightDerivedFunctorPlusCompUnit (moduleDirectImage f Λ)
        (SheafOfModules.toSheaf (constantRing S Λ))).app K ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (moduleDirectImageUnderlyingIso f Λ)).hom.app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit
        (SheafOfModules.toSheaf (constantRing X Λ)) (directImage f)).app K := by
  exact Functor.rightDerivedFunctorPlusThreeFactorIso_unit_app
    (moduleDirectImage f Λ) (SheafOfModules.toSheaf (constantRing S Λ))
    (SheafOfModules.toSheaf (constantRing X Λ)) (directImage f)
    (moduleDirectImageUnderlyingIso f Λ) K

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
