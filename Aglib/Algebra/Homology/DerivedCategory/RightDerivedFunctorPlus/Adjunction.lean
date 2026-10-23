/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Complex
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Postcomposition
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# The actual bounded-below derived adjunction

An additive adjunction with homology-preserving left adjoint induces an
adjunction on the installed bounded-below derived functors. Its unit and
counit retain the original localization factorization equations. The proof
uses native bounded-below injective models, not an unbounded existence claim.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v' w w'

namespace CategoryTheory.Adjunction

open CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B] [EnoughInjectives B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] [L.PreservesHomology]

/-- An exact left adjoint and its right adjoint give the canonical adjunction between
these same installed bounded-below derived functors. -/
def rightDerivedFunctorPlus (adj : L ⊣ R) :
    L.rightDerivedFunctorPlus ⊣ R.rightDerivedFunctorPlus := by
  letI := L.isLeftDerivedFunctor_rightDerivedFunctorPlus
  letI := L.isLeftDerivedFunctor_rightDerivedFunctorPlus_postcomp R.rightDerivedFunctorPlus
  letI := R.isRightDerivedFunctor_rightDerivedFunctorPlus_postcomp L.rightDerivedFunctorPlus
  exact adj.mapCochainComplexPlus.derived
    (CochainComplex.Plus.quasiIso A) (CochainComplex.Plus.quasiIso B)
    L.rightDerivedFunctorPlusExactComparison.hom R.rightDerivedFunctorPlusUnit

/-- The derived adjunction unit factors through the original complex adjunction unit
and the installed right-derived comparison. -/
@[reassoc]
theorem rightDerivedFunctorPlus_unit_fac (adj : L ⊣ R) (K : CochainComplex.Plus A) :
    adj.rightDerivedFunctorPlus.unit.app (DerivedCategory.Plus.Q.obj K) ≫
        R.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlusExactComparison.hom.app K) =
      DerivedCategory.Plus.Q.map (adj.mapCochainComplexPlus.unit.app K) ≫
        R.rightDerivedFunctorPlusUnit.app (L.mapCochainComplexPlus.obj K) := by
  let := L.isLeftDerivedFunctor_rightDerivedFunctorPlus
  let := L.isLeftDerivedFunctor_rightDerivedFunctorPlus_postcomp R.rightDerivedFunctorPlus
  let := R.isRightDerivedFunctor_rightDerivedFunctorPlus_postcomp L.rightDerivedFunctorPlus
  exact adj.mapCochainComplexPlus.derivedη_fac_app (CochainComplex.Plus.quasiIso A)
    L.rightDerivedFunctorPlusExactComparison.hom R.rightDerivedFunctorPlusUnit K

/-- The derived adjunction counit factors through the installed right-derived unit
and the original complex adjunction counit. -/
@[reassoc]
theorem rightDerivedFunctorPlus_counit_fac (adj : L ⊣ R) (K : CochainComplex.Plus B) :
    L.rightDerivedFunctorPlus.map (R.rightDerivedFunctorPlusUnit.app K) ≫
        adj.rightDerivedFunctorPlus.counit.app (DerivedCategory.Plus.Q.obj K) =
      L.rightDerivedFunctorPlusExactComparison.hom.app (R.mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Plus.Q.map (adj.mapCochainComplexPlus.counit.app K) := by
  let := L.isLeftDerivedFunctor_rightDerivedFunctorPlus
  let := L.isLeftDerivedFunctor_rightDerivedFunctorPlus_postcomp R.rightDerivedFunctorPlus
  let := R.isRightDerivedFunctor_rightDerivedFunctorPlus_postcomp L.rightDerivedFunctorPlus
  exact adj.mapCochainComplexPlus.derivedε_fac_app (CochainComplex.Plus.quasiIso B)
    L.rightDerivedFunctorPlusExactComparison.hom R.rightDerivedFunctorPlusUnit K

end CategoryTheory.Adjunction
