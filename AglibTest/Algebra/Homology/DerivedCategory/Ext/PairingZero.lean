/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingZero

/-! Original-map examples and approved-axiom guards. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- Degree-zero coefficient identities act on the original independent-universe Ext. -/
example {A : D} {F : C} {r : ℕ} (c : Ext.{w'} A (L.obj F) r) :
    L.extPairing A c (Ext.mk₀ (𝟙 F)) (add_zero r) = c :=
  L.extPairing_mk₀_id_right c

/-- info: 'CategoryTheory.Functor.extPairing_mk₀_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_mk₀_right

/-- info: 'CategoryTheory.Functor.extPairing_mk₀_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_mk₀_left

/-- info: 'CategoryTheory.Functor.extPairing_mk₀_id_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_mk₀_id_right

/-- info: 'CategoryTheory.Functor.extPairing_mk₀_id_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_mk₀_id_left

/-- info: 'CategoryTheory.Functor.extPairingLinearMap_smul_mk₀_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingLinearMap_smul_mk₀_right

/-- info: 'CategoryTheory.Functor.extPairingLinearMap_smul_mk₀_id_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingLinearMap_smul_mk₀_id_right

/-- info: 'CategoryTheory.Functor.extPairingLinearMap_smul_mk₀_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingLinearMap_smul_mk₀_left

/-- info: 'CategoryTheory.Abelian.Ext.mk₀_nsmul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.Ext.mk₀_nsmul
