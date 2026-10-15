/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedFlatBaseChange.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 78]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # The original bounded-below flat base-change map -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- Use the original standard derived categories of actual module sheaves. -/
local instance derivedFlatBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
/-- The original bounded-below functor of an exact flat pullback. -/
def derivedFlatPullbackPlus {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    DerivedCategory.Plus Y.Modules ⥤ DerivedCategory.Plus X.Modules :=
  (flatExactPullback f).toFunctor.rightDerivedFunctorPlus
/-- Flatness makes the original derived pullback unit invertible on every bounded-below complex. -/
theorem isIso_derivedFlatPullbackPlusUnit {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    IsIso (Scheme.Modules.pullback f).rightDerivedFunctorPlusUnit :=
  (Scheme.Modules.pullback f).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat j]
include h in
/-- The original cartesian square makes its pulled-back leg flat. -/
theorem flat_cartesian_baseChange : Flat a :=
  MorphismProperty.of_isPullback h.flip inferInstance
/-- The actual bounded-below flat base-change map, obtained from the original ordinary mate. -/
def derivedFlatBaseChangeMap :
    letI := flat_cartesian_baseChange a b f j h
    derivedPushforwardPlus f ⋙ derivedFlatPullbackPlus j ⟶
      derivedFlatPullbackPlus a ⋙ derivedPushforwardPlus b := by
  letI := flat_cartesian_baseChange a b f j h
  let F := Scheme.Modules.pushforward f
  let J := Scheme.Modules.pullback j
  let A := Scheme.Modules.pullback a
  let B := Scheme.Modules.pushforward b
  letI := F.isRightDerivedFunctor_comp_of_preservesHomology J
  exact (F.rightDerivedFunctorPlus ⋙ J.rightDerivedFunctorPlus).rightDerivedDesc
    (Functor.rightDerivedFunctorPlusCompUnit F J) (CochainComplex.Plus.quasiIso U.Modules)
    (A.rightDerivedFunctorPlus ⋙ B.rightDerivedFunctorPlus)
    (Functor.whiskerRight (NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h))
      DerivedCategory.Plus.Q ≫ Functor.rightDerivedFunctorPlusCompUnit A B)
/-- The derived comparison retains the original ordinary mate and both composite units. -/
theorem derivedFlatBaseChangeMap_unit (K : CochainComplex.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.pullback j)).app K ≫
      (derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback a)
        (Scheme.Modules.pushforward b)).app K := by
  let := flat_cartesian_baseChange a b f j h
  let F := Scheme.Modules.pushforward f
  let J := Scheme.Modules.pullback j
  let A := Scheme.Modules.pullback a
  let B := Scheme.Modules.pushforward b
  let := F.isRightDerivedFunctor_comp_of_preservesHomology J
  exact Functor.rightDerived_fac_app
    (F.rightDerivedFunctorPlus ⋙ J.rightDerivedFunctorPlus)
    (Functor.rightDerivedFunctorPlusCompUnit F J) (CochainComplex.Plus.quasiIso U.Modules)
    (A.rightDerivedFunctorPlus ⋙ B.rightDerivedFunctorPlus)
    (Functor.whiskerRight (NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h))
      DerivedCategory.Plus.Q ≫ Functor.rightDerivedFunctorPlusCompUnit A B) K
end AlgebraicGeometry.Scheme.Modules
