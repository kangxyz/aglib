/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Full

/-! # Native scalar-restriction comparison and axiom guards -/

@[expose] public noncomputable section

open CategoryTheory

universe c h r m

/-- An original ring-sheaf isomorphism supplies local surjectivity itself. -/
example {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{r}} (e : R ≅ R') (M N : SheafOfModules.{m} R') :
    (M ⟶ N) ≃+ ((SheafOfModules.restrictScalars e.hom).obj M ⟶
      (SheafOfModules.restrictScalars e.hom).obj N) :=
  SheafOfModules.restrictScalarsHomAddEquiv e.hom M N

/-- info: 'SheafOfModules.restrictScalarsFullyFaithfulOfLocallySurjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.restrictScalarsFullyFaithfulOfLocallySurjective

/-- info: 'SheafOfModules.restrictScalarsHomAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.restrictScalarsHomAddEquiv

/-- info: 'SheafOfModules.restrictScalarsHomAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.restrictScalarsHomAddEquiv_apply

/-- info: 'SheafOfModules.restrictScalarsHomAddEquiv_symm_apply_val_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.restrictScalarsHomAddEquiv_symm_apply_val_app

/-- info: 'SheafOfModules.restrictScalarsHomAddEquiv_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.restrictScalarsHomAddEquiv_comp

/-- info: 'SheafOfModules.restrictScalarsCoyonedaIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.restrictScalarsCoyonedaIso

/-- info: 'SheafOfModules.restrictScalarsCoyonedaIso_hom_app_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.restrictScalarsCoyonedaIso_hom_app_apply
