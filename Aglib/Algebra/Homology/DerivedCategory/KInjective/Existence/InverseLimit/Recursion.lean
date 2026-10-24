/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InverseLimit.PrimitiveFamily

/-!
# Actual well-founded recursion on compatible primitives

The recurrence is on native elements of the component complexes. This is the
intermediate extension theorem: predecessor exactness remains an explicit input
until the separate nested-initial-segment induction discharges it.
-/

@[expose] public noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex.InverseLimit

variable {J : Type w} [PartialOrder J]
  (hr : WellFounded ((· < ·) : J → J → Prop))
  (F : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
  [∀ (i : J) (n : ℤ), HasLimit
    (predecessors F i ⋙ HomologicalComplex.eval AddCommGrpCat (.up ℤ) n)]

include hr in
/-- Construct a simultaneous compatible primitive family by actual well-founded
recursion, using the full predecessor-limit comparison at each stage. -/
lemma exists_compatible_primitives (n : ℤ)
    (hstage : ∀ i, (F.obj (op i)).ExactAt n)
    (hpred : ∀ i, (limit (predecessors F i)).ExactAt (n - 1))
    (hsurj : ∀ i, Function.Surjective ((predecessorComparison F i).f (n - 2)))
    (x : ∀ i, (F.obj (op i)).X n) (hx : Compatible F n x)
    (hcycle : ∀ i, (F.obj (op i)).d n (n + 1) (x i) = 0) :
    ∃ z : ∀ i, (F.obj (op i)).X (n - 1),
      (∀ i, (F.obj (op i)).d (n - 1) n (z i) = x i) ∧ Compatible F (n - 1) z := by
  let P (i : J) : Type u := {z : (F.obj (op i)).X (n - 1) //
    (F.obj (op i)).d (n - 1) n z = x i}
  have hP (i : J) : Nonempty (P i) := by
    obtain ⟨z, hz⟩ := exists_primitive_of_exactAt n (hstage i) (x i) (hcycle i)
    exact ⟨⟨z, hz⟩⟩
  let : ∀ i, Nonempty (P i) := hP
  let R : ∀ i j, j < i → P i → P j → Prop :=
    fun _ _ h zi zj => (F.map (homOfLE h.le).op).f (n - 1) zi.val = zj.val
  have extend : ∀ i (z : ∀ j, j < i → P j),
      WellFounded.PredecessorCoherent (r := ((· < ·) : J → J → Prop)) P R i z →
      ∃ y : P i, ∀ j (hj : j < i), R i j hj y (z j hj) := by
    intro i z hz
    have hzc : Compatible (predecessors F i) (n - 1)
        (fun j => (z j.val j.property).val) := by
      apply compatible_of_strict
      intro j k hkj
      exact hz j.val j.property k.val k.property hkj
    obtain ⟨y, hy, hcompat⟩ := extend_primitive F n x hx hcycle i (hstage i)
      (hpred i) (hsurj i) (fun j => (z j.val j.property).val)
      (fun j => (z j.val j.property).property) hzc
    exact ⟨⟨y, hy⟩, fun j hj => hcompat ⟨j, hj⟩⟩
  let z := WellFounded.coherentChoice hr P R extend
  refine ⟨fun i => (z i).val, fun i => (z i).property, ?_⟩
  apply compatible_of_strict
  exact WellFounded.coherentChoice_compatible hr P R extend

end CochainComplex.InverseLimit
