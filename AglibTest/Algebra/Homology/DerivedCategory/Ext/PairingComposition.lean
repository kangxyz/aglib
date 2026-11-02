/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingComposition

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
  {L M N : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [M.Additive] [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]

/-- Composing natural transformations uses the original composite coefficient morphisms. -/
example (τ : L ⟶ M) (σ : M ⟶ N) {A : D} {F G : C} {r s t : ℕ}
    (c : Ext.{w'} A (L.obj F) r) (e : Ext.{w} F G s) (h : r + s = t) :
    N.extPairing A (c.comp (Ext.mk₀ (τ.app F ≫ σ.app F)) (add_zero r)) e h =
      (L.extPairing A c e h).comp (Ext.mk₀ (τ.app G ≫ σ.app G)) (add_zero t) :=
  Functor.extPairing_natTrans (τ ≫ σ) c e h

/-- info: 'CategoryTheory.Functor.extPairingHom_natTrans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingHom_natTrans

/-- info: 'CategoryTheory.Functor.extPairing_natTrans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_natTrans

/-- info: 'CategoryTheory.Functor.extPairingCompAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingCompAddEquiv

/-- info: 'CategoryTheory.Functor.extPairingCompAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingCompAddEquiv_apply

/-- info: 'CategoryTheory.Functor.extPairingCompAddEquiv_symm_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingCompAddEquiv_symm_apply

/-- info: 'CategoryTheory.Functor.extPairingCounitNatTrans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingCounitNatTrans

/-- info: 'CategoryTheory.Functor.extPairingCounitNatTrans_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingCounitNatTrans_app

/-- info: 'CategoryTheory.Functor.extPairingCounitNatTrans_trans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingCounitNatTrans_trans

/-- info: 'CategoryTheory.Functor.extPairingHom_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingHom_comp

/-- info: 'CategoryTheory.Functor.extPairing_mapExt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_mapExt

/-- info: 'CategoryTheory.Functor.extEquiv_mk₀_counit_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extEquiv_mk₀_counit_comp

/-- info: 'CategoryTheory.Functor.extPairing_eq_comp_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairing_eq_comp_counit

/-- info: 'CategoryTheory.Functor.extPairingDualHom_eq_comp_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingDualHom_eq_comp_counit

/-- info: 'CategoryTheory.Functor.extPairingTransposeHom_restriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingTransposeHom_restriction
