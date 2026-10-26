/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.RightAdjoint.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Injective.Restriction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Comparison.ThreeFactor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# The native bounded-below closed right adjoint and open locality

Derive the single selected ordinary closed right adjoint on the original
categories of all module sheaves. Its ordinary open comparison induces a
native derived isomorphism. Exactness of source restriction and preservation
of injectives by target restriction supply the original composition maps.
The defining unit equation retains the same ordinary exchange. No QC
preservation or purity theorem is assumed in this construction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category structure on the indicated module category. -/
local instance closedRightAdjointStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The actual right-derived functor of the sole ordinary closed right adjoint. -/
def derivedClosedImmersionRightAdjointPlus {U X : Scheme.{u}}
    (f : U ⟶ X) [IsClosedImmersion f] :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory.Plus U.Modules :=
  (closedImmersionRightAdjoint f).rightDerivedFunctorPlus

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j]
  [IsClosedImmersion f] [IsClosedImmersion b] (h : IsPullback a b f j)

local instance closedRightAdjointSourceComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison
      (closedImmersionRightAdjoint f) (restrictFunctor a)) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology _ _

local instance closedRightAdjointTargetComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison
      (restrictFunctor j) (closedImmersionRightAdjoint b)) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_preservesInjectives _ _

/-- The native derived closed right adjoint commutes with original open
restriction on all bounded-below module complexes. -/
def derivedClosedImmersionRightAdjointOpenIso :
    (closedImmersionRightAdjoint f).rightDerivedFunctorPlus ⋙
        (restrictFunctor a).rightDerivedFunctorPlus ≅
      (restrictFunctor j).rightDerivedFunctorPlus ⋙
        (closedImmersionRightAdjoint b).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusThreeFactorIso
    (closedImmersionRightAdjoint f) (restrictFunctor a)
    (restrictFunctor j) (closedImmersionRightAdjoint b)
    (closedImmersionRightAdjointOpenIso a b f j h)

/-- The shared constructor retains the original homology and injective-preservation factors. -/
theorem derivedClosedImmersionRightAdjointOpenIso_eq_original :
    derivedClosedImmersionRightAdjointOpenIso a b f j h =
      ((closedImmersionRightAdjoint f).rightDerivedFunctorPlusCompIsoOfPreservesHomology
        (restrictFunctor a)).symm ≪≫
      (closedImmersionRightAdjoint f ⋙ restrictFunctor a).rightDerivedFunctorPlusIso
        (closedImmersionRightAdjointOpenIso a b f j h) ≪≫
      (restrictFunctor j).rightDerivedFunctorPlusCompIsoOfPreservesInjectives
        (closedImmersionRightAdjoint b) := by
  rw [derivedClosedImmersionRightAdjointOpenIso, Functor.rightDerivedFunctorPlusThreeFactorIso,
    Functor.rightDerivedFunctorPlusCompIso_eq_of_preservesHomology,
    Functor.rightDerivedFunctorPlusCompIso_eq_of_preservesInjectives]

/-- The actual derived open comparison is normalized by the original
ordinary open comparison and both installed composite-derived units. -/
@[reassoc]
theorem derivedClosedImmersionRightAdjointOpenIso_unit
    (K : CochainComplex.Plus X.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit (closedImmersionRightAdjoint f)
        (restrictFunctor a)).app K ≫
      (derivedClosedImmersionRightAdjointOpenIso a b f j h).hom.app
        (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (closedImmersionRightAdjointOpenIso a b f j h)).hom.app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (restrictFunctor j)
        (closedImmersionRightAdjoint b)).app K := by
  exact Functor.rightDerivedFunctorPlusThreeFactorIso_unit_app
    (closedImmersionRightAdjoint f) (restrictFunctor a)
    (restrictFunctor j) (closedImmersionRightAdjoint b)
    (closedImmersionRightAdjointOpenIso a b f j h) K

end AlgebraicGeometry.Scheme.Modules
