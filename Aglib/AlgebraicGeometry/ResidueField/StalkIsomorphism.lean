/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField

/-! # Actual residue maps induced by original stalk isomorphisms -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If an original stalk map is an isomorphism, so is its original residue map.
No open-immersion or reducedness assumption is added. -/
theorem residueFieldMap_isIso_of_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)] :
    IsIso (f.residueFieldMap x) :=
  (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

end AlgebraicGeometry.Scheme.Hom
