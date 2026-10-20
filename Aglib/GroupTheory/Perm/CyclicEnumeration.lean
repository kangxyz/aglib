/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Enumerating a finite transitive permutation


Source: `R5Lab.Aglib.GroupTheory.Perm.CyclicEnumeration`.
Packet SHA-256:
`9c3006a56681d7c0859c45cb7bf6945c5ac03f87571f883dfffe52dedfe75f3b`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

section
noncomputable section
open Fin.NatCast
namespace Equiv.Perm.TransitiveCycle
variable {I : Type u} [Fintype I] (σ : Equiv.Perm I)
    (hσ : ∀ v w, σ.SameCycle v w) (a : I)

include hσ in
/-- A transitive permutation is a cycle on the entire actual finite type. -/
theorem isCycleOn_univ : σ.IsCycleOn (Finset.univ : Finset I) := by
  classical
  simp only [Finset.coe_univ]
  exact ⟨σ.bijective.bijOn_univ, fun _ _ _ _ => hσ _ _⟩

/-- Enumerate a finite transitive permutation by its actual successive powers,
starting at a chosen member. Neither a period nor its cardinality is supplied. -/
def enumeration : Fin (Fintype.card I) ≃ I := by
  classical
  refine Equiv.ofBijective (fun j => (σ ^ j.val) a) ⟨?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact ((isCycleOn_univ σ hσ).pow_apply_eq_pow_apply
      (Finset.mem_univ a) |>.mp hij).eq_of_lt_of_lt i.isLt j.isLt
  · intro b
    obtain ⟨n, hn, he⟩ := (isCycleOn_univ σ hσ).exists_pow_eq
      (Finset.mem_univ a) (Finset.mem_univ b)
    exact ⟨⟨n, hn⟩, he⟩

@[simp] theorem enumeration_apply (j : Fin (Fintype.card I)) :
    enumeration σ hσ a j = (σ ^ j.val) a := rfl

/-- The enumeration identifies the constructed permutation with literal
cyclic rotation, including singleton cycles. -/
theorem enumeration_rotate (j : Fin (Fintype.card I)) :
    enumeration σ hσ a (finRotate _ j) = σ (enumeration σ hσ a j) := by
  classical
  let := j.neZero
  simp only [enumeration_apply]
  rw [← Equiv.Perm.mul_apply, ← pow_succ']
  apply ((isCycleOn_univ σ hσ).pow_apply_eq_pow_apply (Finset.mem_univ a)).mpr
  change (finRotate _ j).val % Fintype.card I = (j.val + 1) % Fintype.card I
  have hval : (finRotate _ j).val = (j.val + 1) % Fintype.card I := by
    simp [finRotate_apply, Fin.val_add, Nat.add_mod]
  rw [hval, Nat.mod_mod]

include hσ in
/-- The actual cardinality is a period of the permutation at every point. -/
theorem pow_card_apply (b : I) : (σ ^ Fintype.card I) b = b := by
  classical
  exact (isCycleOn_univ σ hσ).pow_card_apply (Finset.mem_univ b)


/-- Natural powers of literal cyclic rotation are addition in the finite ring. -/
theorem finRotate_pow_apply (m n : ℕ) [NeZero m] (i : Fin m) :
    (finRotate m ^ n) i = i + (n : Fin m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, finRotate_apply]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]

/-- Every orbit of literal cyclic rotation has precisely its stated period. -/
theorem finRotate_pow_eq_iff (m n : ℕ) [NeZero m] (i : Fin m) :
    (finRotate m ^ n) i = i ↔ m ∣ n := by
  rw [finRotate_pow_apply, add_eq_left, Fin.natCast_eq_zero]

include hσ in
/-- Any equivariant map from a finite transitive permutation to the literal
m-cycle forces m to divide the actual cardinality. -/
theorem card_dvd_of_rotating_map (m : ℕ) (p : I → Fin m)
    (hp : ∀ v, p (σ v) = finRotate m (p v)) (a : I) : m ∣ Fintype.card I := by
  let := (p a).neZero
  have hpow (n : ℕ) (v : I) : p ((σ ^ n) v) = (finRotate m ^ n) (p v) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', Equiv.Perm.mul_apply, hp, ih]
  apply (finRotate_pow_eq_iff m (Fintype.card I) (p a)).mp
  rw [← hpow, pow_card_apply σ hσ]

/-- Changing only the proof of a cycle length preserves literal rotation. -/
theorem finCongr_rotate {r s : ℕ} (h : r = s) (j : Fin r) :
    finCongr h (finRotate r j) = finRotate s (finCongr h j) := by
  subst s
  rfl

end Equiv.Perm.TransitiveCycle

end -- noncomputable section
end
