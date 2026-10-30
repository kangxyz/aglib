/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.ZModEndomorphisms

/-! Original-map examples and approved-axiom guards. -/

@[expose] public noncomputable section

open CategoryTheory

/-- Composite moduli use the original additive endomorphisms. -/
example : Function.Bijective (fun a : ZMod 6 =>
    a.val • 𝟙 (AddCommGrpCat.of (ULift (ZMod 6)))) :=
  AddCommGrpCat.uLiftZMod_nsmul_id_bijective 6

/-- Modulus one is retained without a nontriviality premise. -/
example : Function.Bijective (fun a : ZMod 1 =>
    a.val • 𝟙 (AddCommGrpCat.of (ULift (ZMod 1)))) :=
  AddCommGrpCat.uLiftZMod_nsmul_id_bijective 1

/-- info: 'AddCommGrpCat.uLiftZMod_nsmul_id_bijective' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AddCommGrpCat.uLiftZMod_nsmul_id_bijective
