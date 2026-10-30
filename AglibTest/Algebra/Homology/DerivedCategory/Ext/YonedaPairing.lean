/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.YonedaPairing

/-!
# Generic provider tests

These in-package checks retain independent universes and the approved axiom boundary
for every new public declaration in the corresponding provider.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] (A : D)

/-- The signed square works for independent Ext universes and arbitrary total degree. -/
example {S : ShortComplex C} (hS : S.ShortExact) (G : C) (d s : ℕ) (hs : s + 1 ≤ d)
    (e : Ext.{w} S.X₁ G s) (c : Ext.{w'} A (L.obj S.X₃) (d - (s + 1))) :
    L.extPairingTransposeHom A S.X₃ G d (s + 1) hs (Ext.δ hS s (s + 1) rfl e) c =
      ((s + 1 : ℕ) : ℤ).negOnePow •
        L.extPairingTransposeHom A S.X₁ G d s (by lia) e
          (c.comp (hS.map_of_exact L).extClass (by lia)) := by
  exact DFunLike.congr_fun (Functor.extPairingTransposeHom_δ hS G d s hs e) c

/-- info: 'CategoryTheory.Functor.extPairing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing

/-- info: 'CategoryTheory.Functor.extPairing_def' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_def

/-- info: 'CategoryTheory.Functor.extPairingHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingHom

/-- info: 'CategoryTheory.Functor.extPairingHom_apply_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingHom_apply_apply

/-- info: 'CategoryTheory.Functor.extPairing_add_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_add_left

/-- info: 'CategoryTheory.Functor.extPairing_add_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_add_right

/-- info: 'CategoryTheory.Functor.extPairing_zero_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_zero_left

/-- info: 'CategoryTheory.Functor.extPairing_zero_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_zero_right

/-- info: 'CategoryTheory.Functor.extPairing_neg_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_neg_left

/-- info: 'CategoryTheory.Functor.extPairing_neg_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_neg_right

/-- info: 'CategoryTheory.Functor.extPairing_zsmul_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_zsmul_right

/-- info: 'CategoryTheory.Functor.extPairing_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_naturality

/-- info: 'CategoryTheory.Functor.extPairing_comp_mk₀' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_comp_mk₀

/-- info: 'CategoryTheory.Functor.extPairing_extClass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_extClass

/-- info: 'CategoryTheory.Functor.extPairing_δ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_δ

/-- info: 'CategoryTheory.Functor.extPairingDualHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingDualHom

/-- info: 'CategoryTheory.Functor.extPairingDualHom_apply_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingDualHom_apply_apply

/-- info: 'CategoryTheory.Functor.extPairingDualHom_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingDualHom_naturality

/-- info: 'CategoryTheory.Functor.extPairingDualHom_extClass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingDualHom_extClass

/-- info: 'CategoryTheory.Functor.extPairingDualHom_δ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingDualHom_δ

/-- info: 'CategoryTheory.Functor.extPairingTransposeHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingTransposeHom

/-- info: 'CategoryTheory.Functor.extPairingTransposeHom_apply_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingTransposeHom_apply_apply

/-- info: 'CategoryTheory.Functor.extPairingTransposeHom_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingTransposeHom_naturality

/-- info: 'CategoryTheory.Functor.extPairingTransposeHom_extClass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingTransposeHom_extClass

/-- info: 'CategoryTheory.Functor.extPairingTransposeHom_δ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingTransposeHom_δ
