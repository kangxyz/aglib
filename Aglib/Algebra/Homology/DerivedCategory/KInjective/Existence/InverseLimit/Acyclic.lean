/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InverseLimit.Exactness
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InverseLimit.Nested

/-!
# Acyclic inverse limits with entire-predecessor surjectivity

This is the compatible-primitive argument of Stacks 0AAT. Well-founded induction
proves, rather than assumes, acyclicity of all predecessor limits. The hypothesis
is degreewise surjectivity onto each complete predecessor limit, not pairwise
surjectivity of transition maps. The carrier is the native categorical limit.
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
  (hstage : ∀ i, (F.obj (op i)).Acyclic)
  (hsurj : ∀ (i : J) (n : ℤ), Function.Surjective ((predecessorComparison F i).f n))

include hr hstage hsurj in
/-- Every entire predecessor limit is acyclic, by well-founded induction. -/
lemma predecessors_acyclic (i : J) : (limit (predecessors F i)).Acyclic := by
  induction i using hr.induction with
  | h i ih =>
    intro n
    apply exactAt_of_exactAt_predecessors (hr.onFun (f := fun j : Set.Iio i => j.val))
      (predecessors F i) n
    · intro j
      exact hstage j.val n
    · intro j
      exact (ih j.val j.property (n - 1)).of_iso (nestedLimitIso F i j).symm
    · intro j
      exact predecessorComparison_nested_surjective F i j (n - 2) (hsurj j.val (n - 2))

variable [∀ n : ℤ, HasLimit (F ⋙ HomologicalComplex.eval AddCommGrpCat (.up ℤ) n)]

include hr hstage hsurj in
/-- The native limit of this inverse diagram is acyclic. No predecessor-exactness
assumption remains: it is supplied by the preceding well-founded proof. -/
lemma acyclic_limit_of_surjective_predecessorComparison : (limit F).Acyclic := by
  intro n
  exact exactAt_of_exactAt_predecessors hr F n (fun i => hstage i n)
    (fun i => predecessors_acyclic hr F hstage hsurj i (n - 1))
    (fun i => hsurj i (n - 2))

end CochainComplex.InverseLimit
