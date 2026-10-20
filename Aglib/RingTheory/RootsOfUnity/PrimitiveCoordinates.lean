/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.Galois
public import Aglib.RingTheory.RootsOfUnity.BaseField
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Coordinates supplied by a primitive root

A specified primitive root identifies its actual root group with the cyclic
additive group; the chosen root and positive-level condition remain explicit.
-/

@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity.PrimitiveCoordinates
open Field.absoluteGaloisGroup.RootsOfUnity
universe u
variable (K : Type u) [Field K] (n : ℕ) [NeZero n]

/-- The canonical cyclic coordinate supplied by an actual primitive root. -/
def rootEquivZMod (a : Mu K n)
    (ha : IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) n) :
    ZMod n ≃+ Mu K n :=
  ha.zmodEquivZPowers.trans (MulEquiv.subgroupCongr ha.zpowers_eq).toAdditive

@[simp]
theorem rootEquivZMod_one (a : Mu K n)
    (ha : IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) n) :
    rootEquivZMod K n a ha 1 = a := by
  unfold rootEquivZMod
  rw [AddEquiv.trans_apply]
  have h := ha.zmodEquivZPowers_apply_coe_nat 1
  simp only [Nat.cast_one, pow_one] at h
  rw [h]
  rfl

@[simp]
theorem rootEquivZMod_symm_root (a : Mu K n)
    (ha : IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) n) :
    (rootEquivZMod K n a ha).symm a = 1 := by
  apply (rootEquivZMod K n a ha).injective
  simp

/-- Every actual root is an integral multiple of the primitive generator. -/
theorem exists_zsmul_root (a : Mu K n)
    (ha : IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) n) (x : Mu K n) :
    ∃ k : ℤ, x = k • a := by
  obtain ⟨r, rfl⟩ := (rootEquivZMod K n a ha).surjective x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective r
  refine ⟨k, ?_⟩
  simpa using map_zsmul (rootEquivZMod K n a ha) k (1 : ZMod n)

/-- Multiplication of cyclic coordinates as a biadditive map on actual roots. -/
def rootProductHom (a : Mu K n)
    (ha : IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) n) :
    Mu K n →+ Mu K n →+ Mu K n where
  toFun x :=
    { toFun := fun y => (rootEquivZMod K n a ha)
        ((rootEquivZMod K n a ha).symm x * (rootEquivZMod K n a ha).symm y)
      map_zero' := by simp
      map_add' y z := by simp [mul_add] }
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp [add_mul]

/-- The cyclic product is balanced over ℤ. -/
theorem rootProductHom_balanced (a : Mu K n)
    (ha : IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) n)
    (k : ℤ) (x y : Mu K n) :
    rootProductHom K n a ha (k • x) y = rootProductHom K n a ha x (k • y) := by
  rw [map_zsmul, map_zsmul]
  rfl

omit [NeZero n] in
/-- The image of a primitive base-field root remains primitive in the closure. -/
theorem baseRoot_primitive (ζ : rootsOfUnity n K)
    (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) n) :
    IsPrimitiveRoot ((Field.absoluteGaloisGroup.RootsOfUnity.baseRoot K n ζ).toMul :
      (AlgebraicClosure K)ˣ) n := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  change IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) ((ζ : Kˣ) : K)) n
  exact hζ.map_of_injective (algebraMap K (AlgebraicClosure K)).injective

end Field.absoluteGaloisGroup.RootsOfUnity.PrimitiveCoordinates
