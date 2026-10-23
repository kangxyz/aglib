/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.IdealTwist.Evaluation
public import Aglib.AlgebraicGeometry.HilbertScheme.IdealTwist.BaseChange

/-! Focused consumer of the base change of `π_* I_Z(r)` along `baseChangeMap` and of the
evaluation form `Z(K) = Z` of a Hilbert family (Nitsure, arXiv:math/0504590v1, §5, p. 26), with
axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

/-- **Base change**: `f^* π_* I_Z(r) ≅ π'_* I_{Z'}(r)` for `Z' = Z.comap (baseChangeMap ...)`. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {T T' : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
    {g' : T' ⟶ Spec (CommRingCat.of A)} (f : T' ⟶ T) (h : f ≫ g = g')
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj
          (familyIdealTwist ι g Z r)) ≅
      (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g')).obj
        (familyIdealTwist ι g' (Z.comap (baseChangeMap ι g g' f h)) r) :=
  hZ.pushforwardFamilyIdealTwistBaseChangeIso ι f h n e r hr

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistedEvaluationMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistedEvaluationMap_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.evaluationIdeal_eq_of_epi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.evaluationIdeal_eq_of_epi

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.evaluationIdeal_eq_of_epi_homEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.evaluationIdeal_eq_of_epi_homEquiv

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.isIso_cartesianBaseChangeMap_baseChangeMap_familyIdealTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.isIso_cartesianBaseChangeMap_baseChangeMap_familyIdealTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.pushforwardFamilyIdealTwistBaseChangeIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.pushforwardFamilyIdealTwistBaseChangeIso
