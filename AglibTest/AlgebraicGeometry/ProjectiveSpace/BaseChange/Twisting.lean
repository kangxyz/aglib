/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting

/-! Focused consumer of the base change of the twisting sheaves: `π^* O_R(d) ≅ O_S(d)` for every
ring map, every coordinate type and every degree; its frame identities on the charts; the
twisted-module form `π^*(O_R(d) ⊗ M) ≅ O_S(d) ⊗ π^* M`; and the matching transition units. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (ι : Type u)

/-- Twisting sheaves commute with every coefficient base change. -/
example (d : ℤ) :
    (Scheme.Modules.pullback (ProjectiveSpace.map φ ι)).obj (twistingSheaf R ι d) ≅
      twistingSheaf S ι d :=
  twistingPullbackIso φ ι d

/-- The field-extension case used by Mumford's bound. -/
example (k K : Type u) [Field k] [Field K] [Algebra k K] (d : ℤ) :
    (Scheme.Modules.pullback (ProjectiveSpace.map (algebraMap k K) ι)).obj
        (twistingSheaf k ι d) ≅ twistingSheaf K ι d :=
  twistingPullbackIso (algebraMap k K) ι d

-- Applying the frame equivalence on the section ring `Γ(P_S, V)` needs the library's
-- transparency setting, as in the source files.
set_option backward.isDefEq.respectTransparency false in
/-- The pulled-back frame `Xᵢ^d` goes to the frame `Xᵢ^d`, with frame coefficient one. -/
example (d : ℤ) (i : ι) {V : (ProjectiveSpace S ι).Opens} (hV : V ≤ coordinateOpen S ι i) :
    twistingSectionsEquiv S ι d i hV
        ((twistingPullbackIso φ ι d).hom.val.app (op V) (twistingPullbackGenerator φ ι d i hV)) =
      1 := by
  rw [twistingPullbackIso_hom_generator, twistingSectionsEquiv_generator]

-- Applying `twistingSectionsEquiv`, stated on `(twistingSheaf S ι d).val.obj (op V)`, to a section
-- `s : Γ(twistingSheaf S ι d, V)` needs the library's transparency setting.
set_option backward.isDefEq.respectTransparency false in
/-- On chart subopens the inverse is the frame coefficient times the pulled-back frame. -/
example (d : ℤ) (i : ι) {V : (ProjectiveSpace S ι).Opens} (hV : V ≤ coordinateOpen S ι i)
    (s : Γ(twistingSheaf S ι d, V)) :
    (twistingPullbackIso φ ι d).inv.val.app (op V) s =
      twistingSectionsEquiv S ι d i hV s • twistingPullbackGenerator φ ι d i hV :=
  twistingPullbackIso_inv_app φ ι d i hV s

/-- Twisting commutes with pullback, in the module form used for fibres of twists. -/
example (d : ℤ) (M : (ProjectiveSpace R ι).Modules) :
    (Scheme.Modules.pullback (ProjectiveSpace.map φ ι)).obj
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj M) ≅
      (moduleTensorLeftFunctor (ProjectiveSpace S ι) (twistingSheaf S ι d)).obj
        ((Scheme.Modules.pullback (ProjectiveSpace.map φ ι)).obj M) :=
  twistingTensorPullbackIso φ ι d M

/--
info: 'AlgebraicGeometry.ProjectiveSpace.appLE_coordinateTransitionOn'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.appLE_coordinateTransitionOn

/--
info: 'AlgebraicGeometry.ProjectiveSpace.transitionPullback_coordinateUnitCocycle'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.transitionPullback_coordinateUnitCocycle

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingPullbackIso'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingPullbackIso

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingPullbackIso_hom_generator'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingPullbackIso_hom_generator

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingPullbackIso_inv_generator'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingPullbackIso_inv_generator

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingPullbackIso_inv_app'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingPullbackIso_inv_app

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorPullbackIso'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorPullbackIso
