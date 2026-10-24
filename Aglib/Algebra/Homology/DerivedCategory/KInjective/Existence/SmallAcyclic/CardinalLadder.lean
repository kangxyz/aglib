/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.ExactStep

/-!
# Cardinal bounds for a countable downward exactness construction

The cardinal successor operation is chosen from the proved exactness step.
Starting with a bound on the separator, its natural-number iterates have one
common regular upper bound. This supplies a single bound for all degrees of
the forthcoming small acyclic complex, independent of the ambient complex.
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)

/-- The cardinal obtained from the proved uniform exactness step. -/
def exactStepCardinal (κ : Cardinal.{w}) : Cardinal.{w} :=
  (exists_regular_cardinal_exact_step hG κ).choose

lemma exactStepCardinal_isRegular (κ : Cardinal.{w}) :
    (exactStepCardinal hG κ).IsRegular :=
  (exists_regular_cardinal_exact_step hG κ).choose_spec.1

/-- The exactness step with its constructed, rather than supplied, bound. -/
lemma exists_exact_step (κ : Cardinal.{w}) (S : ShortComplex C) (hS : S.Exact)
    {A B : C} (a : A ⟶ S.X₂) [Mono a] (b : B ⟶ S.X₃) (δ : A ⟶ B)
    (hδ : δ ≫ b = a ≫ S.g) (hA : HasCardinalLT (Subobject A) κ) :
    ∃ (X : C) (i : X ⟶ S.X₁) (e : X ⟶ kernel δ),
      Mono i ∧ Epi e ∧ i ≫ S.f = e ≫ kernel.ι δ ≫ a ∧
        HasCardinalLT (Subobject X) (exactStepCardinal hG κ) ∧
        (ShortComplex.mk (e ≫ kernel.ι δ) δ (by simp)).Exact :=
  (exists_regular_cardinal_exact_step hG κ).choose_spec.2 S hS a b δ hδ hA

/-- A bound on the separator and its successive exactness-step bounds. -/
def smallAcyclicCardinalLadder : ℕ → Cardinal.{w}
  | 0 => (HasCardinalLT.exists_regular_cardinal.{w} (Subobject G)).choose
  | n + 1 => exactStepCardinal hG (smallAcyclicCardinalLadder n)

lemma hasCardinalLT_separator_ladder_zero :
    HasCardinalLT (Subobject G) (smallAcyclicCardinalLadder hG 0) :=
  (HasCardinalLT.exists_regular_cardinal.{w} (Subobject G)).choose_spec.2

@[simp]
lemma smallAcyclicCardinalLadder_succ (n : ℕ) :
    smallAcyclicCardinalLadder hG (n + 1) =
      exactStepCardinal hG (smallAcyclicCardinalLadder hG n) := rfl

/-- One regular cardinal exceeds all degreewise bounds in the ladder. -/
lemma exists_regular_cardinal_above_smallAcyclic_ladder :
    ∃ κ : Cardinal.{w}, κ.IsRegular ∧ ∀ n, smallAcyclicCardinalLadder hG n < κ := by
  obtain ⟨κ, hκ, h⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w}
    (fun n : ℕ ↦ (smallAcyclicCardinalLadder hG n).out)
  refine ⟨κ, hκ, fun n ↦ ?_⟩
  have hn := (hasCardinalLT_iff_cardinal_mk_lt _ _).1 (h n)
  simpa using hn

/-- A fixed regular bound for the countable downward construction. -/
def smallAcyclicCardinal : Cardinal.{w} :=
  (exists_regular_cardinal_above_smallAcyclic_ladder hG).choose

lemma smallAcyclicCardinal_isRegular : (smallAcyclicCardinal hG).IsRegular :=
  (exists_regular_cardinal_above_smallAcyclic_ladder hG).choose_spec.1

lemma smallAcyclicCardinalLadder_lt (n : ℕ) :
    smallAcyclicCardinalLadder hG n < smallAcyclicCardinal hG :=
  (exists_regular_cardinal_above_smallAcyclic_ladder hG).choose_spec.2 n

end CategoryTheory.IsGrothendieckAbelian
