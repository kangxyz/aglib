/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.LeftExactComparison

/-! # Original internal-Ext provider axiom guards -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe c d v e e'

/-- An injective target supplies its actual acyclicity without a derived-category model input. -/
example {C : Type c} [Category.{v} C] [Abelian C] [EnoughInjectives C] [HasExt.{e} C]
    {D : Type d} [Category.{v} D] [Abelian D] [EnoughInjectives D] [HasExt.{e'} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] (A : D) (X : C)
    (a : L ⋙ preadditiveCoyoneda.obj (op A) ≅ preadditiveCoyoneda.obj (op X))
    (hI : ∀ (I : C) [Injective I] (q : ℕ), Subsingleton (Ext.{e'} A (L.obj I) (q + 1)))
    (B : C) [Injective B] (q : ℕ) : Ext.{e} X B q ≃+ Ext.{e'} A (L.obj B) q :=
  Functor.extAddEquivOfLeftExactAcyclic L A a hI B
    (fun n => L.isZero_rightDerived_obj_injective_succ n B) q

/-- info: 'CategoryTheory.Functor.leftExactDerivedObjIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.leftExactDerivedObjIso

/-- info: 'CategoryTheory.Functor.leftExactDerivedObjIso_hom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.leftExactDerivedObjIso_hom

/-- info: 'CategoryTheory.Functor.leftExactDerivedObjIso_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.leftExactDerivedObjIso_unit

/-- info: 'CategoryTheory.Functor.leftExactDerivedObjIso_singleUnit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.leftExactDerivedObjIso_singleUnit

/-- info: 'CategoryTheory.Functor.rightDerivedHomIsoOfAcyclic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.rightDerivedHomIsoOfAcyclic

/-- info: 'CategoryTheory.Functor.rightDerivedHomIsoOfAcyclic_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.rightDerivedHomIsoOfAcyclic_naturality

/-- info: 'CategoryTheory.Functor.rightDerivedHomIsoOfAcyclic_zero_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.rightDerivedHomIsoOfAcyclic_zero_unit

/-- info: 'CategoryTheory.Functor.extAddEquivOfLeftExactAcyclic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extAddEquivOfLeftExactAcyclic

/-- info: 'CategoryTheory.Functor.extAddEquivOfLeftExactAcyclic_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extAddEquivOfLeftExactAcyclic_apply

/-- info: 'CategoryTheory.Functor.extAddEquivOfLeftExactAcyclic_mk₀' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extAddEquivOfLeftExactAcyclic_mk₀

/-- info: 'CategoryTheory.Functor.extAddEquivOfLeftExactAcyclic_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extAddEquivOfLeftExactAcyclic_naturality


/-- info: 'CategoryTheory.Functor.leftExactDerivedReverse' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.leftExactDerivedReverse

/-- info: 'CategoryTheory.Functor.leftExactDerivedReverse_app_comp_comparison' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.leftExactDerivedReverse_app_comp_comparison

/-- info: 'CategoryTheory.Functor.leftExactDerivedReverse_app_eq_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.leftExactDerivedReverse_app_eq_inv

/-- info: 'CategoryTheory.Functor.leftExactDerivedReverse_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.leftExactDerivedReverse_naturality

/-- info: 'CategoryTheory.Functor.isIso_representedRightDerivedUnit_map_of_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.isIso_representedRightDerivedUnit_map_of_injective

/-- info: 'CategoryTheory.Functor.representedDerivedImage_isZero_of_ext_subsingleton' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.representedDerivedImage_isZero_of_ext_subsingleton

/-- info: 'CategoryTheory.Functor.rightDerivedSingleUnitNatTrans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.rightDerivedSingleUnitNatTrans

/-- info: 'CategoryTheory.Functor.rightDerivedSingleUnitNatTrans_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.rightDerivedSingleUnitNatTrans_app

/-- info: 'CategoryTheory.Functor.rightDerivedRepresentedReverse' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.rightDerivedRepresentedReverse

/-- info: 'CategoryTheory.Functor.rightDerivedHomReverse' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.rightDerivedHomReverse

/-- info: 'CategoryTheory.Functor.rightDerivedHomReverse_app_eq_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.rightDerivedHomReverse_app_eq_inv

/-- info: 'CategoryTheory.Functor.extReverseOfLeftExact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extReverseOfLeftExact

/-- info: 'CategoryTheory.Functor.extReverseOfLeftExact_eq_symm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extReverseOfLeftExact_eq_symm

/-- info: 'CategoryTheory.Functor.extReverseOfLeftExact_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extReverseOfLeftExact_naturality

/-- info: 'CategoryTheory.Functor.extReverseOfLeftExact_mk₀' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extReverseOfLeftExact_mk₀
