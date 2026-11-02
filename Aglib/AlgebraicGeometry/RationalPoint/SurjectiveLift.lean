/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.JacobsonSpace

/-!
# Actual geometric-point lifts through surjective locally finite type maps

The literal pullback fibre is nonempty and locally of finite type over
the specified algebraically closed field. Its native Jacobson closed
point gives an actual K-section. Composing with the original first
projection gives the desired original scheme-morphism lift.

No properness, flatness, finite fibre cardinality or replacement fibre
model is used. Algebraic closedness is retained explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every specified algebraically closed field fibre has an actual section
over that SAME field, in the literal original pullback. -/
theorem exists_fibre_section_of_isAlgClosed (K : Type u) [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ Y) :
    ∃ s : Spec (.of K) ⟶ pullback f t, s ≫ pullback.snd f t = 𝟙 _ := by
  let p : pullback (C := Scheme.{u}) f t ⟶ Spec (.of K) := pullback.snd f t
  have : Surjective p := inferInstanceAs (Surjective (pullback.snd f t))
  have : LocallyOfFiniteType p := inferInstanceAs (LocallyOfFiniteType (pullback.snd f t))
  obtain ⟨x, _⟩ := p.surjective (IsLocalRing.closedPoint K)
  have : Nonempty (pullback (C := Scheme.{u}) f t) := ⟨x⟩
  have : JacobsonSpace (pullback (C := Scheme.{u}) f t) := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set (pullback (C := Scheme.{u}) f t)).Nonempty)
    isOpen_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint p z hz, pointOfClosedPoint_comp p z hz⟩

/-- Surjective locally finite type morphisms lift every original
algebraically closed field test as an ACTUAL scheme morphism. -/
theorem exists_lift_spec_of_isAlgClosed (K : Type u) [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ Y) : ∃ u : Spec (.of K) ⟶ X, u ≫ f = t := by
  obtain ⟨s, hs⟩ := exists_fibre_section_of_isAlgClosed f K t
  refine ⟨s ≫ pullback.fst f t, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]

end AlgebraicGeometry.Scheme.Hom
