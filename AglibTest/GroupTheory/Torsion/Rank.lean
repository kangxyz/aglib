/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.GroupTheory.Torsion.Rank
import Mathlib.Tactic.NormNum

open AddSubgroup.TorsionBy

noncomputable section

example (T : Type*) [AddCommGroup T] (r n : ℕ) (hn : 0 < n)
    (hc : ∀ d : ℕ, d ∣ n → Nat.card (AddSubgroup.torsionBy T (d : ℤ)) = d ^ r) :
    Nonempty (AddSubgroup.torsionBy T (n : ℤ) ≃+ (Fin r → ZMod n)) :=
  nonempty_torsionEquiv_of_card_pow T r n hn hc

example (T : Type*) [AddCommGroup T] (r : ℕ) :
    Nonempty (AddSubgroup.torsionBy T (1 : ℤ) ≃+ (Fin r → ZMod 1)) := by
  apply nonempty_torsionEquiv_of_card_pow T r 1 (by decide)
  intro d hd
  have : d = 1 := Nat.dvd_one.mp hd
  subst d
  have : Subsingleton (AddSubgroup.torsionBy T (1 : ℤ)) := ⟨fun x y => by
    apply Subtype.ext
    have hx := AddSubgroup.torsionBy.nsmul_iff.mp x.property
    have hy := AddSubgroup.torsionBy.nsmul_iff.mp y.property
    simpa only [one_nsmul] using hx.trans hy.symm⟩
  simp

example (T : Type*) [AddCommGroup T] (n : ℕ) [Module (ZMod n) T]
    (e : T ≃+ (Fin 0 → ZMod n)) : Module.Basis (Fin 0) (ZMod n) T :=
  basisOfEquivRank 0 n e

-- The top-level cardinality alone does not characterize a composite-level module.
example : Nat.card (ZMod 2 × ZMod 2) = 4 := by
  norm_num [Nat.card_prod, Nat.card_zmod]

example : ¬ Nonempty ((ZMod 2 × ZMod 2) ≃+ ZMod 4) := by
  rintro ⟨e⟩
  have hkill (x : ZMod 4) : 2 • x = 0 := by
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_nsmul]
    have hy : 2 • y = 0 :=
      Prod.ext (ZModModule.char_nsmul_eq_zero 2 y.1)
        (ZModModule.char_nsmul_eq_zero 2 y.2)
    rw [hy, map_zero]
  have h : (2 : ZMod 4) = 0 := by simpa using hkill 1
  exact (by decide : (2 : ZMod 4) ≠ 0) h

/-- info: 'AddSubgroup.TorsionBy.nonempty_torsionEquiv_of_card_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AddSubgroup.TorsionBy.nonempty_torsionEquiv_of_card_pow

/-- info: 'AddSubgroup.TorsionBy.basisOfEquivRank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AddSubgroup.TorsionBy.basisOfEquivRank
