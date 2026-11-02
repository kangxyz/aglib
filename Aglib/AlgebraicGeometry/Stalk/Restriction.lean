/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The original stalk map inside an actual isomorphism restriction

The native restriction square identifies its original stalk-map arrows.
The existing actual point-blowup calculation is factored here once, with
an arbitrary morphism and original target open. No geometric hypothesis
besides the genuine restriction isomorphism and point membership is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An actual isomorphism restriction makes the original stalk map an
isomorphism at each original source point lying over that same open. -/
theorem isIso_stalkMap_of_isIso_morphismRestrict
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)]
    (y : Y) (hy : f y ∈ U) : IsIso (f.stalkMap y) := by
  let p : (f ⁻¹ᵁ U).toScheme := ⟨y, hy⟩
  let e := Scheme.Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion
    (isPullback_morphismRestrict f U).flip p y rfl
  exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff e).mpr inferInstance

end AlgebraicGeometry.Scheme.Hom
