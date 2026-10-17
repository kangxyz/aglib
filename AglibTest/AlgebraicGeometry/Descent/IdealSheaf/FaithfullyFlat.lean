/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Descent.IdealSheaf.FaithfullyFlat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-! Focused consumer of faithfully flat descent of closed subschemes (Nitsure,
arXiv:math/0504590v1, Lemma 6.7). The morphism `f` is flat, surjective and
quasi-compact; pullback of ideal sheaves is Mathlib's `Scheme.IdealSheafData.comap`. The last
example records that the coequalizer half, Lemma 6.7(1), is supplied by Mathlib's `EffectiveEpi`
instance for such morphisms. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f]

/-- Lemma 6.7(2) for ideal sheaves: existence and uniqueness of the descended ideal sheaf. -/
example (Z : X.IdealSheafData)
    (hZ : Z.comap (pullback.fst f f) = Z.comap (pullback.snd f f)) :
    ∃! Q : Y.IdealSheafData, Q.comap f = Z :=
  Scheme.IdealSheafData.existsUnique_comap_eq_of_flat_of_surjective f Z hZ

/-- The descended ideal sheaf is the pushforward. -/
example (Z : X.IdealSheafData)
    (hZ : Z.comap (pullback.fst f f) = Z.comap (pullback.snd f f)) :
    (Z.map f).comap f = Z :=
  Scheme.IdealSheafData.comap_map_eq_self_of_flat_of_surjective f Z hZ

example (Z : X.IdealSheafData) :
    (∃ Q : Y.IdealSheafData, Q.comap f = Z) ↔
      Z.comap (pullback.fst f f) = Z.comap (pullback.snd f f) :=
  Scheme.IdealSheafData.exists_comap_eq_iff_of_flat_of_surjective f Z

/-- Lemma 6.7(2), closed-immersion form, with the base-changed morphism flat, surjective and
quasi-compact. -/
example {T : Scheme.{u}} (i : T ⟶ X) [IsClosedImmersion i]
    (hi : i.ker.comap (pullback.fst f f) = i.ker.comap (pullback.snd f f)) :
    ∃ (Q : Y.IdealSheafData) (q : T ⟶ Q.subscheme),
      IsPullback i q f Q.subschemeι ∧ Flat q ∧ Surjective q ∧ QuasiCompact q :=
  ⟨_, _, isPullback_lift_ker_comp_of_flat_of_surjective f i hi,
    flat_surjective_quasiCompact_lift_ker_comp_of_flat_of_surjective f i hi⟩

/-- Uniqueness of the descended closed subscheme in closed-immersion form. -/
example {T Q : Scheme.{u}} {i : T ⟶ X} {q : T ⟶ Q} {j : Q ⟶ Y} [IsClosedImmersion j]
    (H : IsPullback i q f j) : j.ker = (i ≫ f).ker :=
  ker_eq_ker_comp_of_isPullback_of_flat_of_surjective f H

/-- Lemma 6.7(1), supplied by Mathlib: `f` is a coequalizer of the two projections. -/
noncomputable example :
    IsColimit (Cofork.ofπ f pullback.condition : Cofork (pullback.fst f f) (pullback.snd f f)) :=
  isColimitCoforkOfEffectiveEpi f _ (pullback.isLimit _ _)

/-- info: 'AlgebraicGeometry.Scheme.IdealSheafData.comap_comap_fst_eq_comap_comap_snd_of_comp_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.comap_comap_fst_eq_comap_comap_snd_of_comp_eq

/-- info: 'AlgebraicGeometry.Scheme.IdealSheafData.comap_comap_fst_eq_comap_comap_snd' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.comap_comap_fst_eq_comap_comap_snd

/-- info: 'AlgebraicGeometry.Scheme.IdealSheafData.comap_map_eq_self_of_flat_of_surjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.comap_map_eq_self_of_flat_of_surjective

/-- info: 'AlgebraicGeometry.Scheme.IdealSheafData.existsUnique_comap_eq_of_flat_of_surjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.existsUnique_comap_eq_of_flat_of_surjective

/-- info: 'AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_iff_of_flat_of_surjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.exists_comap_eq_iff_of_flat_of_surjective

/-- info: 'AlgebraicGeometry.isPullback_lift_ker_comp_of_flat_of_surjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isPullback_lift_ker_comp_of_flat_of_surjective

/-- info: 'AlgebraicGeometry.flat_surjective_quasiCompact_lift_ker_comp_of_flat_of_surjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_surjective_quasiCompact_lift_ker_comp_of_flat_of_surjective

/-- info: 'AlgebraicGeometry.ker_eq_ker_comp_of_isPullback_of_flat_of_surjective' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ker_eq_ker_comp_of_isPullback_of_flat_of_surjective
