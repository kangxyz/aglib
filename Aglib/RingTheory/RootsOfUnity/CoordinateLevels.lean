/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.Coordinates
public import Aglib.RingTheory.RootsOfUnity.Exactness
public import Aglib.Data.ZMod.CoefficientMaps

/-!
# Root coordinates across divisible levels

A primitive top root supplies the lower root by the actual power map. Its
exponent coordinates commute with the canonical ZMod reduction map.
-/

@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity.CoordinateLevels
open Field.absoluteGaloisGroup.RootsOfUnity
  Field.absoluteGaloisGroup.RootsOfUnity.PrimitiveCoordinates
universe u
variable (K : Type u) [Field K]
section OneLevel
variable (n : ℕ) [NeZero n] (a : Mu K n)
  (ha : IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) n)
/-- Root exponent coordinates supplied by an actual primitive root. -/
def rootCoordinates : Mu K n ≃+ ZMod n := (rootEquivZMod K n a ha).symm

@[simp] theorem rootCoordinates_root : rootCoordinates K n a ha a = 1 :=
  rootEquivZMod_symm_root K n a ha

@[simp] theorem rootCoordinates_symm_one : (rootCoordinates K n a ha).symm 1 = a :=
  rootEquivZMod_one K n a ha

variable [CharZero K]
/-- Every primitive-root coordinate has the same actual cyclotomic action. -/
theorem rootCoordinates_smul (g : Field.absoluteGaloisGroup K) (x : Mu K n) :
    rootCoordinates K n a ha (g • x) =
      (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character K n g : ZMod n) *
        rootCoordinates K n a ha x := by
  rw [Field.absoluteGaloisGroup.RootsOfUnity.Coordinates.root_smul_eq_nsmul, map_nsmul,
    nsmul_eq_mul, ZMod.natCast_zmod_val]

end OneLevel
section Pair
variable (d e : ℕ) [NeZero d] [NeZero e]
/-- A primitive top root gives the lower root by the actual power reduction. -/
def reducedRoot (a : Mu K (d * e)) : Mu K d :=
  Field.absoluteGaloisGroup.RootsOfUnity.Reduction.muReduction K d e a

omit [NeZero d] in
/-- The lower root is genuinely primitive, by the established power-root theorem. -/
theorem reducedRoot_primitive (a : Mu K (d * e))
    (ha : IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) (d * e)) :
    IsPrimitiveRoot ((reducedRoot K d e a).toMul : (AlgebraicClosure K)ˣ) d :=
  Field.absoluteGaloisGroup.RootsOfUnity.Exactness.muReduction_primitive K d e (NeZero.pos e) a ha

omit [NeZero d] [NeZero e] in
/-- Compatibility is an actual equality of root values, not supplied coordinate data. -/
@[simp] theorem reducedRoot_value (a : Mu K (d * e)) :
    ((reducedRoot K d e a).toMul : (AlgebraicClosure K)ˣ) =
      (a.toMul : (AlgebraicClosure K)ˣ) ^ e := rfl

variable (a : Mu K (d * e))
  (ha : IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) (d * e))

/-- Coordinates from the compatible pair make the genuine root power map
ordinary reduction of root exponents. -/
theorem rootCoordinates_reduction (x : Mu K (d * e)) :
    rootCoordinates K d (reducedRoot K d e a) (reducedRoot_primitive K d e a ha)
      (Field.absoluteGaloisGroup.RootsOfUnity.Reduction.muReduction K d e x) =
      (ZMod.castHom (dvd_mul_right d e) (ZMod d)) (rootCoordinates K (d * e) a ha x)
        := by
  obtain ⟨k, rfl⟩ := exists_zsmul_root K (d * e) a ha x
  rw [map_zsmul, map_zsmul, map_zsmul, rootCoordinates_root, map_zsmul, map_one]
  exact congrArg (fun z : ZMod d => k • z)
    (rootCoordinates_root K d (reducedRoot K d e a) (reducedRoot_primitive K d e a ha))

variable [CharZero K]
/-- The compatible lower generator constructed from the canonical chosen top root. -/
def lowerGenerator : Mu K d := reducedRoot K d e
  (Field.absoluteGaloisGroup.RootsOfUnity.Coordinates.generator K (d * e))

theorem lowerGenerator_primitive :
    IsPrimitiveRoot ((lowerGenerator K d e).toMul : (AlgebraicClosure K)ˣ) d :=
  reducedRoot_primitive K d e (Field.absoluteGaloisGroup.RootsOfUnity.Coordinates.generator K (d *
    e))
    (Field.absoluteGaloisGroup.RootsOfUnity.Coordinates.generator_primitive K (d * e))

/-- The chosen pair satisfies the root-power relation in the actual algebraic closure. -/
@[simp] theorem lowerGenerator_value :
    (((lowerGenerator K d e).toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot K (d * e) ^ e := by
  change (((Field.absoluteGaloisGroup.RootsOfUnity.Coordinates.generator K (d * e)).toMul :
    (AlgebraicClosure K)ˣ) :
    AlgebraicClosure K) ^ e = _
  rw [Field.absoluteGaloisGroup.RootsOfUnity.Coordinates.generator_value]

end Pair
end Field.absoluteGaloisGroup.RootsOfUnity.CoordinateLevels
