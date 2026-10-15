/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Geometric points of finite surjective morphisms

This module proves the geometric-point existence input in
`K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex` at revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

Base change to an algebraically closed field gives a nonempty affine scheme
finite over that field. A closed point supplies an actual field-valued section.
The resulting lift is a scheme morphism, and the relative formulation proves
equality of the entire morphisms in the category of schemes over the base.
No étale hypothesis or rational point over the field of definition is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Finite.GeometricPoints

universe u

/-- `K2-018#prop:k2018-arithmetic-characters` at revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`: every algebraically closed
field-valued point lifts through a finite surjective scheme morphism.
The conclusion is equality of scheme morphisms, without an étale assumption. -/
theorem exists_lift {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    {K : Type u} [Field K] [IsAlgClosed K] (y : Spec (CommRingCat.of K) ⟶ Y) :
    ∃ x : Spec (CommRingCat.of K) ⟶ X, x ≫ f = y := by
  obtain ⟨z, _⟩ := (Limits.pullback.snd f y).surjective (default : Spec (CommRingCat.of K))
  obtain ⟨p, _, hp⟩ :=
    (isClosed_univ : IsClosed
      (Set.univ : Set (Limits.pullback f y : Scheme.{u}))).exists_closed_singleton
      ⟨z, trivial⟩
  refine ⟨pointOfClosedPoint (Limits.pullback.snd f y) p hp ≫ Limits.pullback.fst f y, ?_⟩
  rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
    Category.id_comp]

/-- `K2-018#prop:k2018-arithmetic-characters` at revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`: the relative geometric-point
lifting statement. It applies over any base scheme, hence in particular over
`Spec F` for an arbitrary field `F`, and proves equality of the full `Over` maps. -/
theorem exists_lift_over {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (hfinite : IsFinite f.left) (hsurjective : Surjective f.left)
    (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (y : Over.mk s ⟶ Y) :
    ∃ x : Over.mk s ⟶ X, x ≫ f = y := by
  let := hfinite
  let := hsurjective
  obtain ⟨x, hx⟩ := exists_lift f.left y.left
  refine ⟨Over.homMk x ?_, ?_⟩
  · rw [← Over.w f, ← Category.assoc, hx]
    exact Over.w y
  · exact Over.OverMorphism.ext hx

end AlgebraicGeometry.Scheme.Finite.GeometricPoints
