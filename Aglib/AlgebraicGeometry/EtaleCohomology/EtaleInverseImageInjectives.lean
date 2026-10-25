/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceSheaves
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Injectives

/-! # Original étale inverse image preserves injective sheaves

The actual small étale slice equivalence identifies restriction with the
original slice pullback. The original inverse-image comparison then transports
injectivity, without a new extension-by-zero construction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]

/-- Actual restriction to an étale chart preserves injective abelian sheaves. -/
instance etaleRestriction_preservesInjectiveObjects :
    (etaleRestriction f).PreservesInjectiveObjects where
  injective_obj {I} hI := by
    let : Injective I := hI
    let : AB4OfSize.{u} AddCommGrpCat.{u + 1} :=
      Sheaf.SliceCohomology.abelianGroupsAB4OfSize.{u, u + 1}
    let U : X.Etale := Scheme.Etale.mk f
    exact Injective.of_iso ((etaleSliceRestrictionIso U).app I) inferInstance

/-- The existing inverse-image functor along an étale morphism preserves injectives. -/
instance inverseImage_preservesInjectiveObjects_of_etale :
    (inverseImage f).PreservesInjectiveObjects where
  injective_obj {I} hI := by
    let : Injective I := hI
    exact Injective.of_iso ((inverseImageEtaleIso f).symm.app I) inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology
