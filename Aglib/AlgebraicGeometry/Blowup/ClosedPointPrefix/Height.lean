/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix.Reroot
public import Mathlib.Order.KonigLemma
public import Mathlib.Data.Nat.Find

/-!
# Least empty levels of the original finite point prefixes

Native Konig's lemma applies to the original truncations and finite parent
fibres. Rerooting the same prefixes makes their least empty level decrease at
every actual child. Geometric finiteness and the no-infinite-path proof remain
separate inputs; there is no new tree or path construction.
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix

variable {eligible : (Y : Scheme.{u}) → Y → Prop} {X : Scheme.{u}} {x : X}

/-- Native Konig applied to the original finite-prefix truncations. -/
theorem exists_empty_level_of_no_compatible_sequence
    (hfin : ∀ n (p : Prefix eligible X x n),
      Finite {q : Prefix eligible X x (n + 1) // parent q = p})
    (hno : ¬ ∃ b : (n : ℕ) → Prefix eligible X x n,
      ∀ n, parent (b (n + 1)) = b n) :
    ∃ n : ℕ, IsEmpty (Prefix eligible X x n) := by
  classical
  by_contra h
  let : Finite (Prefix eligible X x 0) := inferInstanceAs (Finite PUnit.{u + 1})
  have hn (n : ℕ) : Nonempty (Prefix eligible X x n) := by
    by_contra hn
    exact h ⟨n, ⟨fun p => hn ⟨p⟩⟩⟩
  let : ∀ n, Nonempty (Prefix eligible X x n) := hn
  have hf (n : ℕ) (p : Prefix eligible X x n) :
      {q : Prefix eligible X x (n + 1) | truncate (Nat.le_add_right n 1) q = p}.Finite := by
    apply (Set.finite_coe_iff.mp (hfin n p)).subset
    intro q hq
    exact ((truncate_succ (Nat.le_refl n) q).trans (truncate_refl (parent q))).symm.trans hq
  obtain ⟨b, hb⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun n => Prefix eligible X x n) truncate
    (fun _ p => truncate_refl p) (fun _ _ _ hij hjk p => truncate_trans hij hjk p) hf
  apply hno
  refine ⟨b, fun n => ?_⟩
  exact ((truncate_succ (Nat.le_refl n) (b (n + 1))).trans
    (truncate_refl (parent (b (n + 1))))).symm.trans (hb (Nat.le_add_right n 1))

/-- The first empty level of this same original prefix system. -/
def height (h : ∃ n : ℕ, IsEmpty (Prefix eligible X x n)) : ℕ := by
  classical
  exact Nat.find h

theorem height_empty (h : ∃ n : ℕ, IsEmpty (Prefix eligible X x n)) :
    IsEmpty (Prefix eligible X x (height h)) := by
  classical
  exact Nat.find_spec h

theorem height_pos (h : ∃ n : ℕ, IsEmpty (Prefix eligible X x n)) : 0 < height h := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hzero : IsEmpty (Prefix eligible X x 0) :=
    Eq.mp (congrArg (fun n => IsEmpty (Prefix eligible X x n)) hz) (height_empty h)
  exact hzero.false PUnit.unit

/-- Empty original levels remain empty under the original truncation. -/
theorem empty_level_of_le {n m : ℕ} (h : IsEmpty (Prefix eligible X x n)) (hnm : n ≤ m) :
    IsEmpty (Prefix eligible X x m) := ⟨fun p => h.false (truncate hnm p)⟩

/-- Every actual first child inherits a finite empty level, using the same prepend map. -/
theorem child_exists_empty_level (h : ∃ n : ℕ, IsEmpty (Prefix eligible X x n))
    (y : Child eligible X x) :
    ∃ n : ℕ, IsEmpty
      (Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact False.elim (hn.false PUnit.unit)
  | succ n => exact ⟨n, ⟨fun q => hn.false (prepend y q)⟩⟩

/-- The least empty level strictly decreases at every actual original child. -/
theorem child_height_lt (h : ∃ n : ℕ, IsEmpty (Prefix eligible X x n))
    (y : Child eligible X x)
    (hy : ∃ n : ℕ, IsEmpty
      (Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val n)) :
    height hy < height h := by
  classical
  have hp := height_pos h
  have he : height h - 1 + 1 = height h := Nat.sub_add_cancel (Nat.one_le_of_lt hp)
  have hempty : IsEmpty
      (Prefix eligible (blowupDatum (X.fromSpecResidueField x).ker).Y y.val (height h - 1)) := by
    refine ⟨fun q => ?_⟩
    exact (height_empty h).false (he ▸ prepend y q)
  exact lt_of_le_of_lt (Nat.find_min' hy hempty) (Nat.sub_lt hp (by decide))

end AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
