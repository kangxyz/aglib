/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ZMod

/-!
# Generic provider tests

These in-package checks retain independent universes and the approved axiom boundary
for every new public declaration in the corresponding provider.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- A target annihilator suffices; no annihilator is required on the source. -/
example (n : ℕ) {X Y : C} (hY : n • 𝟙 Y = 0) (q : ℕ) (e : Ext.{w} X Y q) : n • e = 0 :=
  Ext.nsmul_eq_zero_of_nsmul_id_right n hY e

/-- Modulus zero gives the ordinary integer module without a positivity hypothesis. -/
example (X Y : C) (q : ℕ) : Module (ZMod 0) (Ext.{w} X Y q) :=
  Ext.zmodModuleOfNsmulIdLeft 0 (by simp) Y q

/-- info: 'CategoryTheory.Abelian.Ext.nsmul_eq_zero_of_nsmul_id_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.Ext.nsmul_eq_zero_of_nsmul_id_left

/-- info: 'CategoryTheory.Abelian.Ext.nsmul_eq_zero_of_nsmul_id_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.Ext.nsmul_eq_zero_of_nsmul_id_right

/-- info: 'CategoryTheory.Abelian.Ext.zmodModuleOfNsmulIdLeft' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.Ext.zmodModuleOfNsmulIdLeft

/-- info: 'CategoryTheory.Abelian.Ext.zmodModuleOfNsmulIdRight' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.Ext.zmodModuleOfNsmulIdRight

/-- info: 'CategoryTheory.Functor.nsmul_id_eq_zero_obj' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.nsmul_id_eq_zero_obj

/-- info: 'CategoryTheory.Functor.extPairingLinearMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingLinearMap

/-- info: 'CategoryTheory.Functor.extPairingLinearMap_apply_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingLinearMap_apply_apply

/-- info: 'CategoryTheory.Functor.extPairingDualLinearMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingDualLinearMap

/-- info: 'CategoryTheory.Functor.extPairingTransposeLinearMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingTransposeLinearMap
