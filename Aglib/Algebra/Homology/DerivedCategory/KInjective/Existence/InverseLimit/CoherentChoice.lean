/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.Order.WellFounded

/-!
# Well-founded compatible choice

A concrete well-founded recurrence glues dependent choices when every coherent
predecessor family admits an extension. The homological consumer must prove that
extension using the entire predecessor limit, not pairwise transition maps.
-/

@[expose] public noncomputable section

universe w u

namespace WellFounded

variable {J : Type w} {r : J → J → Prop} (hr : WellFounded r)
  (X : J → Type u) [∀ i, Nonempty (X i)]
  (R : ∀ i j, r j i → X i → X j → Prop)

/-- Coherence of the entire family below a stage. -/
def PredecessorCoherent (i : J) (x : ∀ j, r j i → X j) : Prop :=
  ∀ j (hj : r j i) k (hk : r k i) (hkj : r k j), R j k hkj (x j hj) (x k hk)

variable (extend : ∀ i (x : ∀ j, r j i → X j),
  PredecessorCoherent X R i x → ∃ y : X i, ∀ j (hj : r j i), R i j hj y (x j hj))

/-- The actual local choice used by the well-founded recursion. -/
def coherentChoiceStep (i : J) (x : ∀ j, r j i → X j) : X i := by
  classical
  exact if h : PredecessorCoherent X R i x then Classical.choose (extend i x h)
  else Classical.choice (inferInstance : Nonempty (X i))

/-- Actual dependent choices, defined by well-founded recursion. -/
def coherentChoice (i : J) : X i :=
  hr.fix (coherentChoiceStep X R extend) i

lemma coherentChoice_eq (i : J) :
    coherentChoice hr X R extend i =
      coherentChoiceStep X R extend i (fun j _ => coherentChoice hr X R extend j) :=
  hr.fix_eq _ i

/-- Every chosen element agrees with every predecessor, simultaneously. -/
lemma coherentChoice_compatible (i : J) :
    ∀ j (hj : r j i),
      R i j hj (coherentChoice hr X R extend i) (coherentChoice hr X R extend j) := by
  induction i using hr.induction with
  | h i ih =>
    have hc : PredecessorCoherent X R i
        (fun j _ => coherentChoice hr X R extend j) := by
      intro j hj k _hk hkj
      exact ih j hj k hkj
    rw [coherentChoice_eq]
    simp only [coherentChoiceStep, dite_eq_left hc]
    exact Classical.choose_spec (extend i _ hc)

end WellFounded
