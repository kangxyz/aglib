/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit

/-!
# Native integer twists in the Picard group

The original twists and their native tensor isomorphisms define one
integer-to-Picard homomorphism over every commutative ring and coordinate
index type. Integer twist classes are the corresponding integer multiples
of the original O(1) class.

The general construction is extracted from Line/PositiveTwist; its former
Line names remain thin aliases there. No projective-line or field
hypothesis belongs to this constructor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace

section TwistClasses

variable (R : Type u) [CommRing R] (I : Type u)

/-- Actual integer twists, with their native tensor multiplication, define Picard classes. -/
def twistClassHom : ℤ →+ PicardGroup (ProjectiveSpace R I) where
  toFun d := classOf _ (twistingLineBundle R I d)
  map_zero' := Quotient.sound ⟨twistingZeroIso R I ≪≫
    (coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit (ProjectiveSpace R I).ringCatSheaf)).symm⟩
  map_add' a b := Quotient.sound ⟨(twistingTensorIso R I a b).symm⟩

@[simp] theorem twistClassHom_apply (d : ℤ) :
    twistClassHom R I d = classOf _ (twistingLineBundle R I d) := rfl

/-- Integer twist classes are the actual integer multiples of the original O(1) class. -/
theorem twistClassHom_eq_zsmul (d : ℤ) :
    twistClassHom R I d = d • classOf _ (twistingLineBundle R I 1) := by
  simpa only [zsmul_eq_mul, mul_one, Int.cast_id, twistClassHom_apply] using
    map_zsmul (twistClassHom R I) d (1 : ℤ)

end TwistClasses

end AlgebraicGeometry.ProjectiveSpace
