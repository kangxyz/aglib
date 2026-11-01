/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomConstant
public import Aglib.Algebra.Module.ZMod.Injective

/-! # Original constant-chart comparison and lifted-scalar boundary checks -/

@[expose] public noncomputable section

universe w

/-- The already selected lifted scalar ring inherits self-injectivity through its original map. -/
example (n : ℕ) [NeZero n] :
    Module.Injective (ULift.{w} (ZMod n)) (ULift.{w} (ZMod n)) := by
  let : Module.Injective (ZMod n) (ZMod n) := ZMod.injective_self n
  let e : ZMod n ≃+* ULift.{w} (ZMod n) := ULift.ringEquiv.symm
  exact Module.Injective.of_ringEquiv e e.toSemilinearEquiv

/-- info: 'ModuleCat.Sheaf.ConstantRing.constantFrameSourceIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.constantFrameSourceIso

/-- info: 'ModuleCat.Sheaf.ConstantRing.constantFrameHomNatIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.constantFrameHomNatIso

/-- info: 'ModuleCat.Sheaf.ConstantRing.constantFrameSectionAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.constantFrameSectionAddEquiv

/-- info: 'ModuleCat.Sheaf.ConstantRing.constantFrameSectionAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.constantFrameSectionAddEquiv_apply

/-- info: 'ModuleCat.Sheaf.ConstantRing.sliceFrameHomNatIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.sliceFrameHomNatIso

/-- info: 'ModuleCat.Sheaf.ConstantRing.sliceFrameSectionAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.sliceFrameSectionAddEquiv

/-- info: 'ModuleCat.Sheaf.ConstantRing.sliceFrameSectionAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.sliceFrameSectionAddEquiv_apply
