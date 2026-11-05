/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Affine pullbacks after affine precomposition

An affine morphism above a specified affine pullback has affine total space.
The canonical pullback-pasting isomorphism identifies this with the native
pullback of the original composite. In particular this transports affine
field fibres through a finite cover without affineness of the whole family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- Affineness of the original pullback persists after precomposition by an
affine morphism, using the actual composite and canonical pullbacks. -/
theorem isAffine_pullback_comp_of_isAffineHom
    {Y X S T : Scheme.{u}} (g : Y ⟶ X) [IsAffineHom g]
    (f : X ⟶ S) (b : T ⟶ S) [IsAffine (pullback f b : Scheme.{u})] :
    IsAffine (pullback (g ≫ f) b : Scheme.{u}) := by
  let : IsAffine (pullback g (pullback.fst f b) : Scheme.{u}) := inferInstance
  exact IsAffine.of_isIso (pullbackRightPullbackFstIso f b g).inv

end AlgebraicGeometry.Scheme
