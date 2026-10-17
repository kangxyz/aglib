/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.IdealSheaf.Descent.Pullback

/-! Focused consumer of the pullback properties of ideal sheaves used by faithfully flat descent of
closed subschemes. Pullback is Mathlib's `Scheme.IdealSheafData.comap`.
Checked: flat surjective morphisms have injective section maps and trivial kernel without a
quasi-compactness premise, pullback along them is injective, the affine formulas for pullback and
pushforward, and joint injectivity of pullback along an open cover. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- Flat surjective morphisms are scheme-theoretically dominant by instance. -/
example (f : X ⟶ Y) [Flat f] [Surjective f] : f.ker = ⊥ :=
  f.ker_eq_bot

example (f : X ⟶ Y) [Flat f] [Surjective f] (U : Y.Opens) : Function.Injective (f.app U) :=
  f.app_injective_of_flat_of_surjective U

example (f : X ⟶ Y) [Flat f] [Surjective f] (I : Y.IdealSheafData) : (I.comap f).map f = I :=
  I.map_comap_of_flat_of_surjective f

example [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (I : Y.IdealSheafData) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom :=
  I.ideal_comap_top_of_isAffine f

/-- Ideal sheaves are determined by their pullbacks along an open cover. -/
example (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J :=
  Scheme.IdealSheafData.ext_of_comap_eq 𝒰.f 𝒰.iUnion_range h

/-- info: 'AlgebraicGeometry.Scheme.Hom.app_injective_of_flat_of_surjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.Hom.app_injective_of_flat_of_surjective

/-- info: 'AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_flat_of_surjective' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsSchemeTheoreticallyDominant.of_flat_of_surjective

/-- info: 'AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_flat_of_surjective' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.map_comap_of_flat_of_surjective

/-- info: 'AlgebraicGeometry.Scheme.IdealSheafData.comap_injective_of_flat_of_surjective' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.comap_injective_of_flat_of_surjective

/-- info: 'AlgebraicGeometry.Scheme.IdealSheafData.ideal_map_top_of_isAffine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.ideal_map_top_of_isAffine

/-- info: 'AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_top_of_isAffine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.ideal_comap_top_of_isAffine

/-- info: 'AlgebraicGeometry.Scheme.IdealSheafData.ext_of_comap_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.ext_of_comap_eq

/-- info: 'AlgebraicGeometry.Scheme.Hom.ker_eq_comap_of_isPullback_of_isOpenImmersion' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.Hom.ker_eq_comap_of_isPullback_of_isOpenImmersion
