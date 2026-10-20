/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.PrimitiveCoordinates
public import Aglib.RingTheory.RootsOfUnity.FiniteCharacter

/-!
# Cyclotomic exponent coordinates on actual roots

The selected primitive root is the one used by the native cyclotomic character.
These coordinates intertwine the actual Galois action with that character.
-/

@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity.Coordinates
open Field.absoluteGaloisGroup.RootsOfUnity
  Field.absoluteGaloisGroup.RootsOfUnity.PrimitiveCoordinates
open _root_.Field.absoluteGaloisGroup
universe u
variable (K : Type u) [Field K] [CharZero K] (n : ℕ) [NeZero n]
/-- The actual additive root underlying the primitive root chosen for χₙ. -/
def generator : Mu K n :=
  Additive.ofMul (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot_spec K
    n).toRootsOfUnity

/-- The chosen additive generator has exactly the chosen field root as value. -/
@[simp] theorem generator_value :
    (((generator K n).toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot K n := by
  simp [generator]

/-- The additive generator comes from a genuine primitive unit. -/
theorem generator_primitive :
    IsPrimitiveRoot ((generator K n).toMul : (AlgebraicClosure K)ˣ) n := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  rw [generator_value]
  exact _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot_spec K n

/-- Exponent coordinates on the actual roots, in the same primitive-root basis as χₙ. -/
def rootCoordinates : Mu K n ≃+ ZMod n :=
  (rootEquivZMod K n (generator K n) (generator_primitive K n)).symm

@[simp] theorem rootCoordinates_generator : rootCoordinates K n (generator K n) = 1 :=
  rootEquivZMod_symm_root K n (generator K n) (generator_primitive K n)

@[simp] theorem rootCoordinates_symm_one : (rootCoordinates K n).symm 1 = generator K n :=
  rootEquivZMod_one K n (generator K n) (generator_primitive K n)


/-- The actual Galois action on every root is the constructed cyclotomic exponent. -/
theorem root_smul_eq_nsmul (g : Field.absoluteGaloisGroup K) (x : Mu K n) :
    g • x = (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character K n g : ZMod n).val • x
      := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character_eval K n g
    (((x.toMul : rootsOfUnity n (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ) :
      AlgebraicClosure K)
    (by exact congrArg Units.val ((mem_rootsOfUnity _ _).mp x.toMul.property))

/-- Root exponent coordinates intertwine the actual action and χₙ. -/
theorem rootCoordinates_smul (g : Field.absoluteGaloisGroup K) (x : Mu K n) :
    rootCoordinates K n (g • x) =
      (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character K n g : ZMod n) *
        rootCoordinates K n x := by
  rw [root_smul_eq_nsmul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

end Field.absoluteGaloisGroup.RootsOfUnity.Coordinates
