/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.Perm.FinRotate
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Literal finite-product projections, sections and rotations


Source: `R5Lab.Aglib.Algebra.Ring.Pi.FiniteProjection`.
Packet SHA-256:
`31002cddfdc853fd9b08a4f60bf6ac360e8b7c601c0d90359824b2f06ff7de0e`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
universe u

namespace Fin

section Index
variable (m n : ℕ) [NeZero m]

/-- Actual component index reduction from the mn-cycle to the m-cycle. -/
def mulIndex (i : Fin (m * n)) : Fin m := ⟨i.val % m, Nat.mod_lt _ (NeZero.pos m)⟩

@[simp] theorem mulIndex_rotate (i : Fin (m * n)) :
    mulIndex m n (finRotate (m * n) i) = finRotate m (mulIndex m n i) := by
  let := i.neZero
  apply Fin.ext
  simp only [mulIndex, finRotate_apply, Fin.val_add, Fin.val_one']
  rw [Nat.add_mod_mod, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right m n), Nat.add_mod_mod,
    Nat.mod_add_mod]

/-- Pull back functions by the actual component-index reduction. -/
def repeatTupleMap {A : Type u} [CommRing A] :
    (Fin m → A) →+* (Fin (m * n) → A) :=
  RingHom.pi (fun i => Pi.evalRingHom (fun _ : Fin m => A) (mulIndex m n i))

@[simp] theorem repeatTupleMap_apply {A : Type u} [CommRing A]
    (p : Fin m → A) (i : Fin (m * n)) :
    repeatTupleMap m n p i = p (mulIndex m n i) := rfl

/-- Indexing the mn components by sheet and underlying component. -/
def mulIndexEquiv : Fin (m * n) ≃ Fin n × Fin m :=
  (finCongr (Nat.mul_comm m n)).trans finProdFinEquiv.symm

@[simp] theorem mulIndexEquiv_snd (i : Fin (m * n)) :
    (mulIndexEquiv m n i).2 = mulIndex m n i := rfl

@[simp] theorem mulIndex_equiv_symm (j : Fin n × Fin m) :
    mulIndex m n ((mulIndexEquiv m n).symm j) = j.2 := by
  rw [← mulIndexEquiv_snd, Equiv.apply_symm_apply]


theorem mulIndex_rotate_pow (r : ℕ) (i : Fin (m * n)) :
    mulIndex m n ((finRotate (m * n) ^ r) i) =
      (finRotate m ^ r) (mulIndex m n i) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      mulIndex_rotate, ih]

/-- Rotation by m preserves each component lying under it. -/
theorem mulIndex_rotate_period (i : Fin (m * n)) :
    mulIndex m n ((finRotate (m * n) ^ m) i) = mulIndex m n i := by
  have hm : (finRotate m) ^ m = 1 := by
    simpa only [Equiv.Perm.finRotate_order m] using pow_orderOf_eq_one (finRotate m)
  rw [mulIndex_rotate_pow, hm]
  rfl


variable [NeZero n]

/-- Selecting sheet zero is an actual section of the normalized tuple map. -/
def repeatTupleSection {A : Type u} [CommRing A] :
    (Fin (m * n) → A) →+* (Fin m → A) :=
  RingHom.pi (fun i => Pi.evalRingHom (fun _ : Fin (m * n) => A)
    ((mulIndexEquiv m n).symm (0, i)))

omit [NeZero m] in
@[simp] theorem repeatTupleSection_apply {A : Type u} [CommRing A]
    (p : Fin (m * n) → A) (i : Fin m) :
    repeatTupleSection m n p i = p ((mulIndexEquiv m n).symm (0, i)) := rfl

@[simp] theorem repeatTupleSection_map {A : Type u} [CommRing A] :
    (repeatTupleSection m n (A := A)).comp (repeatTupleMap m n) = RingHom.id _ := by
  apply RingHom.ext
  intro p
  funext i
  exact congrArg p (mulIndex_equiv_symm m n (0, i))

end Index

variable (n : ℕ)

/-- Precomposition on literal product rings. -/
def tuplePerm {A : Type u} [CommRing A] (s : Equiv.Perm (Fin n)) :
    (Fin n → A) →+* (Fin n → A) :=
  (RingEquiv.piCongrLeft' (fun _ : Fin n => A) s.symm).toRingHom

/-- Reindexing by `s.symm` in the canonical equivalence precomposes by `s`. -/
@[simp] theorem tuplePerm_apply {A : Type u} [CommRing A] (s : Equiv.Perm (Fin n))
    (p : Fin n → A) (i : Fin n) : tuplePerm n s p i = p (s i) := rfl

end Fin
