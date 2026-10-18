/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Shift
public import Aglib.Algebra.Homology.CochainComplexPlus.QuasiIsoShift
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TransformationShift

/-!
# Native shifts of the original derived open comparison

The original derived-unit square determines shift compatibility of the
actual open base-change isomorphism. Both sides keep the installed shifts
and the original ordinary Cartesian restriction map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {W X U Y : Scheme.{u}} (i : W ⟶ X) (q : W ⟶ U) (p : X ⟶ Y) (j : U ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)

/-- The original open base-change comparison commutes with its installed integer shifts. -/
instance derivedOpenBaseChangeIso_commShift :
    (derivedOpenBaseChangeIso i q p j H).hom.CommShift ℤ := by
  let P := pushforward p
  let J := restrictFunctor j
  let A := restrictFunctor i
  let B := pushforward q
  let α := Functor.rightDerivedFunctorPlusCompUnit P J
  let β := Functor.whiskerRight
      (NatTrans.mapCochainComplexPlus (cartesianOpenBaseChange i q p j H).hom)
        DerivedCategory.Plus.Q ≫
    Functor.rightDerivedFunctorPlusCompUnit A B
  let : (P.rightDerivedFunctorPlus ⋙ J.rightDerivedFunctorPlus).IsRightDerivedFunctor
      α (CochainComplex.Plus.quasiIso X.Modules) :=
    P.isRightDerivedFunctor_comp_of_preservesHomology J
  let : α.CommShift ℤ := by
    dsimp only [α]
    infer_instance
  let : β.CommShift ℤ := by
    dsimp only [β]
    infer_instance
  exact Functor.commShift_of_rightDerived_factorization DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso X.Modules) α β (derivedOpenBaseChangeIso i q p j H).hom
    (by
      apply NatTrans.ext
      funext K
      exact derivedOpenBaseChangeIso_unit i q p j H K)

end AlgebraicGeometry.Scheme.Modules
