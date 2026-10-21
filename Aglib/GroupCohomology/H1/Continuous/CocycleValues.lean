/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.GroupCohomology.H1.Continuous

/-!
# Continuous cocycle values on conjugates and powers

For a group with a topology acting on an additive topological commutative group, an element
that acts trivially on all coefficients has the stated cocycle values on conjugates and powers.
Group multiplication and the coefficient action need no extra continuity hypotheses for these
identities.

Extraction source: `R5Lab.Aglib.GroupCohomology.H1.CocycleValues`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`a54d951c7fc976ce533b37eb5e206c9bb8ecf0606912f6b7275197a789a138ab`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

open _root_.GroupCohomology.ContinuousH1

namespace GroupCohomology.ContinuousH1.Cocycle
variable {G A : Type*} [Group G] [TopologicalSpace G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A]

/-- A cocycle value on a conjugate transforms by the coefficient action when
the inner element acts trivially. -/
lemma conjugation_value (c : Cocycle G A) (g h : G)
    (hfixed : ∀ a : A, h • a = a) :
    c.val (g * h * g⁻¹) = g • c.val h := by
  have hz : c.val g + g • c.val g⁻¹ = 0 := by
    simpa using (c.map_mul g g⁻¹).symm
  calc
    c.val (g * h * g⁻¹) = c.val g + g • (c.val h + h • c.val g⁻¹) := by
      rw [mul_assoc, c.map_mul, c.map_mul]
    _ = (c.val g + g • c.val g⁻¹) + g • c.val h := by
      rw [hfixed, smul_add]
      abel
    _ = g • c.val h := by rw [hz, zero_add]

/-- Powers of an element acting trivially on coefficients multiply its cocycle
value by the exponent. -/
lemma power_value (c : Cocycle G A) (h : G)
    (hfixed : ∀ a : A, h • a = a) (n : ℕ) :
    c.val (h ^ n) = n • c.val h := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', c.map_mul, hfixed, ih]
    simpa only [add_comm] using (succ_nsmul (c.val h) n).symm

end GroupCohomology.ContinuousH1.Cocycle
