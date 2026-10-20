/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.IsIso.CartesianRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Isomorphism restrictions under base change

Source: `lean/R5Lab/Aglib/AlgebraicGeometry/Morphisms/Isomorphism/BaseChangeRestriction.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `73f6aebc40ee3c51adebfb745b8416b9510aa78f6704c71a919d742a6b39c278`.
Native objects and proved suppliers replace application provenance and redundant premises.
-/

@[expose] public section


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A restriction isomorphism remains an isomorphism on the actual inverse-image open. -/
lemma isIso_restrict_pullback {Y X X' : Scheme.{u}} (f : Y ⟶ X) (t : X' ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] :
    IsIso (pullback.snd f t ∣_ (t ⁻¹ᵁ U)) :=
  isIso_restrict_of_isPullback (IsPullback.of_hasPullback f t).flip U

end AlgebraicGeometry.Scheme.Hom
