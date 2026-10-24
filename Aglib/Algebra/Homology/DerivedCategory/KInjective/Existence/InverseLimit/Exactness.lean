/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InverseLimit.Recursion

/-!
# Exactness from the actual primitive recurrence

This is the native limit consumer of the coherent recurrence. Its predecessor
exactness input is to be discharged by well-founded initial-segment induction.
-/

@[expose] public noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex.InverseLimit

variable {J : Type w} [PartialOrder J]
  (hr : WellFounded ((· < ·) : J → J → Prop))
  (F : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
  [∀ n : ℤ, HasLimit (F ⋙ HomologicalComplex.eval AddCommGrpCat (.up ℤ) n)]
  [∀ (i : J) (n : ℤ), HasLimit
    (predecessors F i ⋙ HomologicalComplex.eval AddCommGrpCat (.up ℤ) n)]

omit [∀ (i : J) (n : ℤ), HasLimit
    (predecessors F i ⋙ HomologicalComplex.eval AddCommGrpCat (.up ℤ) n)] in
/-- Componentwise projections of a native limit element form a compatible family. -/
lemma projections_compatible (n : ℤ) (x : (limit F).X n) :
    Compatible F n (fun i => (limit.π F (op i)).f n x) := by
  intro i j h
  have he := congrArg (fun f => f.f n) (limit.w F (homOfLE h).op)
  exact congrArg (fun f => f x) he

set_option backward.isDefEq.respectTransparency false in
include hr in
/-- Exactness of the entire limit, with predecessor exactness still explicit. -/
lemma exactAt_of_exactAt_predecessors (n : ℤ)
    (hstage : ∀ i, (F.obj (op i)).ExactAt n)
    (hpred : ∀ i, (limit (predecessors F i)).ExactAt (n - 1))
    (hsurj : ∀ i, Function.Surjective ((predecessorComparison F i).f (n - 2))) :
    (limit F).ExactAt n := by
  rw [(limit F).exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)]
  apply ((limit F).sc' (n - 1) n (n + 1)).ab_exact_iff.mpr
  change ∀ x : (limit F).X n, (limit F).d n (n + 1) x = 0 →
    ∃ y : (limit F).X (n - 1), (limit F).d (n - 1) n y = x
  intro x hx
  have hc (i : J) : (F.obj (op i)).d n (n + 1) ((limit.π F (op i)).f n x) = 0 := by
    have he := congrArg (fun f => f x) ((limit.π F (op i)).comm n (n + 1))
    simp only [ConcreteCategory.comp_apply] at he
    rw [he, hx]
    exact map_zero _
  obtain ⟨z, hz, hzc⟩ := exists_compatible_primitives hr F n hstage hpred hsurj
    (fun i => (limit.π F (op i)).f n x) (projections_compatible F n x) hc
  let y := limitElement F (n - 1) (fun i => z i.unop)
    (fun i j f => hzc i.unop j.unop (leOfHom f.unop))
  have hproj (j : Jᵒᵖ) : (limit.π F j).f (n - 1) y = z j.unop :=
    limitElement_π F (n - 1) _ _ j
  refine ⟨y, ?_⟩
  apply limitElement_ext F n
  intro j
  have he := congrArg (fun f => f y) ((limit.π F j).comm (n - 1) n)
  simp only [ConcreteCategory.comp_apply] at he
  rw [← he, hproj]
  exact hz j.unop

end CochainComplex.InverseLimit
