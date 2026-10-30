/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Module.ZMod

/-!
# Endomorphisms of the original lifted cyclic group

For every positive modulus, including one, every additive endomorphism of the
lifted cyclic group is a unique scalar multiple of its identity. The original
additive-category Hom set is retained; there is no chosen basis or free-module
hypothesis on other finite ZMod modules.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AddCommGrpCat

/-- A scalar is recovered uniquely from its multiple of the original cyclic identity. -/
theorem uLiftZMod_nsmul_id_bijective (n : ℕ) [NeZero n] :
    Function.Bijective (fun a : ZMod n =>
      a.val • 𝟙 (AddCommGrpCat.of (ULift.{u} (ZMod n)))) := by
  constructor
  · intro a b h
    have h' := congrArg (fun f => (f (ULift.up 1)).down) h
    change a.val • (1 : ZMod n) = b.val • (1 : ZMod n) at h'
    simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one] using h'
  · intro f
    let a : ZMod n := (f (ULift.up 1)).down
    refine ⟨a, ?_⟩
    apply ConcreteCategory.hom_ext
    intro x
    have hx : x = x.down.val • (ULift.up 1 : ULift.{u} (ZMod n)) := by
      apply ULift.ext
      change x.down = x.down.val • (1 : ZMod n)
      simp only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]
    change a.val • x = f x
    rw [hx, map_nsmul]
    apply ULift.ext
    change a.val • (x.down.val • (1 : ZMod n)) = x.down.val • a
    simp only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]
    exact mul_comm a x.down

end AddCommGrpCat
