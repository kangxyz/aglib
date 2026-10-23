/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceTopology
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Comparison

/-! # Original abelian sheaves on the actual small étale slice -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)

/-- The original sheaf equivalence for the genuine small étale slice. -/
def etaleSliceSheafEquivalence :
    AbelianSheaf.{u, u + 1} U.left ≌
      Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1} :=
  Functor.IsDenseSubsite.sheafEquiv (Scheme.smallEtaleTopology U.left)
    ((Scheme.smallEtaleTopology X).over U) (etaleSliceBackward U) AddCommGrpCat.{u + 1}

instance etaleSliceSheafEquivalence_inverse_additive :
    (etaleSliceSheafEquivalence U).inverse.Additive where
  map_add := by intros; rfl

instance etaleSliceSheafEquivalence_functor_additive :
    (etaleSliceSheafEquivalence U).functor.Additive := by
  let : (etaleSliceSheafEquivalence U).symm.functor.Additive :=
    etaleSliceSheafEquivalence_inverse_additive U
  exact Equivalence.inverse_additive (etaleSliceSheafEquivalence U).symm

/-- Original slice restriction is literal chart restriction under the equivalence. -/
def etaleSliceRestrictionIso :
    (Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U ⋙
        (etaleSliceSheafEquivalence U).inverse ≅ etaleRestriction U.hom :=
  Iso.refl _

/-- The identified constant source uses the actual constant-sheaf adjunction. -/
def etaleSliceConstantIso :
    constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1} ⋙
        (etaleSliceSheafEquivalence U).functor ≅
      constantSheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1} :=
  equivCommuteConstant (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}
    ((Scheme.smallEtaleTopology X).over U) (etaleSliceBackward U)
    (etaleTerminalIsTerminal U.left)
    ((etaleTerminalIsTerminal U.left).isTerminalObj (etaleSliceBackward U))

end AlgebraicGeometry.Scheme.EtaleCohomology
