/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.AffineOpen

/-! Focused consumer of the restriction of `P^n_A ×_{Spec A} S` over the affine opens of `S` and
of its base change along `T ⟶ S`, with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

/-- Over an affine open `U`, the family is `P^n_{Γ(S, U)}`; along `g : T ⟶ S`, the family over
`T` is the base change. -/
example {A : Type u} [CommRing A] (ι : Type u) {S T : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of A))
    (g : T ⟶ S) {U : S.Opens} (hU : IsAffineOpen U) :
    IsPullback (affineBaseMap ι s hU) (toSpec Γ(S, U) ι) (pullback.snd (toSpec A ι) s)
        hU.fromSpec ∧
      IsPullback (pullbackBaseChange ι s g) (pullback.snd (toSpec A ι) (g ≫ s))
        (pullback.snd (toSpec A ι) s) g :=
  ⟨isPullback_affineBaseMap ι s hU, isPullback_pullbackBaseChange ι s g⟩


/--
info: 'AlgebraicGeometry.ProjectiveSpace.specMap_affineBaseRingHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.specMap_affineBaseRingHom

/--
info: 'AlgebraicGeometry.ProjectiveSpace.affineBaseRingHom_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.affineBaseRingHom_restrict

/--
info: 'AlgebraicGeometry.ProjectiveSpace.affineBaseRingHom_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.affineBaseRingHom_comp

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isPullback_affineBaseMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isPullback_affineBaseMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.affineBaseMap_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.affineBaseMap_restrict

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isPullback_pullbackBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isPullback_pullbackBaseChange

/--
info: 'AlgebraicGeometry.ProjectiveSpace.affineBaseMap_pullbackBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.affineBaseMap_pullbackBaseChange

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isLocallyNoetherian_pullback_toSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isLocallyNoetherian_pullback_toSpec
