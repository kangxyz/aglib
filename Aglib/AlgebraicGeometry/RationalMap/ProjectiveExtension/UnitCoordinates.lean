/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitEndomorphisms
public import Aglib.AlgebraicGeometry.Blowup.IdealFrames

/-!
# Pulling back actual scalar coordinates

Conjugation by the native pullback-unit comparison preserves composition of
scheme pullbacks. On affine schemes it takes literal multiplication by `a`
to literal multiplication by its image, including over nonreduced rings.
These equations retain the actual maps needed for projective agreement on a
prescribed principal open.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The scalar coordinate along an actual spectrum map is the original ring
homomorphism applied to the original scalar. -/
theorem pullbackUnitEnd_affine {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : A) :
    pullbackUnitEnd (Spec.map (CommRingCat.ofHom φ))
        (Blowup.IdealFrames.affineMultiplication A a) =
      Blowup.IdealFrames.affineMultiplication B (φ a) := by
  rw [pullbackUnitEnd, Blowup.IdealFrames.affineMultiplication_pullback,
    Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules
