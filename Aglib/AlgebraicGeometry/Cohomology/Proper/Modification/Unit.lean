/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.SingleComparison
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.AlgebraicGeometry.Modules.IsomorphismFunctors
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The original ordinary-pullback unit used by modification descent

For any scheme morphism, the ordinary pullback/pushforward adjunction unit
followed by the original right-derived single comparison gives the native
map from a coefficient's single to the derived pushforward of its ordinary
pullback. This is natural in every actual coefficient. Its formula retains
the original installed derived unit. Properness, flatness and coherence
are not needed to construct it.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The installed standard ambient derived category of actual module sheaves. -/
local instance modificationUnitStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {Y X : Scheme.{u}} (π : Y ⟶ X)

/-- The ordinary adjunction unit followed by the original derived single comparison. -/
def ordinaryModificationUnitNatTrans :
    DerivedCategory.Plus.singleFunctor X.Modules 0 ⟶
      pullback π ⋙ DerivedCategory.Plus.singleFunctor Y.Modules 0 ⋙ derivedPushforwardPlus π :=
  (Functor.leftUnitor (DerivedCategory.Plus.singleFunctor X.Modules 0)).inv ≫
    Functor.whiskerRight (pullbackPushforwardAdjunction π).unit
      (DerivedCategory.Plus.singleFunctor X.Modules 0) ≫
    (Functor.associator (pullback π) (pushforward π)
      (DerivedCategory.Plus.singleFunctor X.Modules 0)).hom ≫
    Functor.whiskerLeft (pullback π) (rightDerivedSingleComparison (pushforward π))

/-- The canonical modification map uses the original ordinary pulled coefficient. -/
abbrev ordinaryModificationUnit (M : X.Modules) :
    (DerivedCategory.Plus.singleFunctor X.Modules 0).obj M ⟶
      (derivedPushforwardPlus π).obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M)) :=
  (ordinaryModificationUnitNatTrans π).app M

/-- The two factors are exactly the original ordinary adjunction unit and
the existing right-derived single comparison. -/
theorem ordinaryModificationUnit_eq (M : X.Modules) :
    ordinaryModificationUnit π M =
      (DerivedCategory.Plus.singleFunctor X.Modules 0).map
          ((pullbackPushforwardAdjunction π).unit.app M) ≫
        (rightDerivedSingleComparison (pushforward π)).app ((pullback π).obj M) := by
  simp only [ordinaryModificationUnit, ordinaryModificationUnitNatTrans,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp]

/-- The original installed derived unit is the last factor of the same canonical map. -/
theorem ordinaryModificationUnit_expanded (M : X.Modules) :
    ordinaryModificationUnit π M =
      (DerivedCategory.Plus.singleFunctor X.Modules 0).map
          ((pullbackPushforwardAdjunction π).unit.app M) ≫
        DerivedCategory.Plus.Q.map
          ((exactSingleComplexNatIso (pushforward π)).inv.app ((pullback π).obj M)) ≫
        (derivedPushforwardPlusUnit π).app
          ((CochainComplex.singleFunctorPlus Y.Modules 0).obj ((pullback π).obj M)) := by
  rw [ordinaryModificationUnit_eq]
  rfl

/-- Coefficient naturality retains the original ordinary pullback map and
the original installed derived pushforward map. -/
@[reassoc]
theorem ordinaryModificationUnit_naturality {M N : X.Modules} (f : M ⟶ N) :
    (DerivedCategory.Plus.singleFunctor X.Modules 0).map f ≫ ordinaryModificationUnit π N =
      ordinaryModificationUnit π M ≫
        (derivedPushforwardPlus π).map
          ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map ((pullback π).map f)) :=
  (ordinaryModificationUnitNatTrans π).naturality f

/-- A scheme isomorphism makes the same ordinary modification map invertible
for every original module coefficient. -/
theorem ordinaryModificationUnit_isIso_of_isIso [IsIso π] (M : X.Modules) :
    IsIso (ordinaryModificationUnit π M) := by
  let := pullback_isEquivalence_of_isIso π
  let := pushforward_isEquivalence_of_isIso π
  let := (pushforward π).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let : IsIso (rightDerivedSingleComparison (pushforward π)) := by
    dsimp only [rightDerivedSingleComparison]
    infer_instance
  rw [ordinaryModificationUnit_eq]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
