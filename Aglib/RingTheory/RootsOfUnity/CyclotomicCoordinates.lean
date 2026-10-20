/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.Coordinates
public import Aglib.RingTheory.RootsOfUnity.FieldPullback
public import Aglib.RingTheory.RootsOfUnity.FiniteCharacter

/-!
# Field extension and primitive-root coordinates

Compatible closure embeddings preserve primitive roots and the actual finite
cyclotomic character. The same chosen-root generator is reused.
-/

@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity.CyclotomicCoordinates
open Field.absoluteGaloisGroup.RootsOfUnity
  Field.absoluteGaloisGroup.RootsOfUnity.PrimitiveCoordinates
open _root_.Field.absoluteGaloisGroup
universe u v w
variable (K : Type u) [Field K] [CharZero K] (n : ℕ) [NeZero n]
/-- The actual action on every root is the cyclotomic exponent, including n=1. -/
theorem mu_smul_eq_nsmul (g : Field.absoluteGaloisGroup K) (x : Mu K n) :
    g • x = (CyclotomicCharacter.character K n g : ZMod n).val • x :=
  Coordinates.root_smul_eq_nsmul K n g x

/-- P1's primitive root, regarded as an element of the actual additive root group. -/
abbrev primitiveMu : Mu K n := Coordinates.generator K n

/-- The selected tensor generator uses literally the primitive root chosen in P1. -/
@[simp] theorem primitiveMu_value :
    (((primitiveMu K n).toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot K n :=
  IsPrimitiveRoot.val_toRootsOfUnity_coe
    (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot_spec K n)

/-- Primitivity is proved from P1's closed-field existence theorem. -/
theorem primitiveMu_spec :
    IsPrimitiveRoot ((primitiveMu K n).toMul : (AlgebraicClosure K)ˣ) n := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  simpa using _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot_spec K n

section FieldExtension
variable (L : Type v) [Field L] [CharZero L] [Algebra K L]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]
omit [CharZero K] [NeZero n] [CharZero L] [Algebra K L]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)] in
/-- The selected closure embedding preserves the actual primitive root. -/
theorem muMap_primitive (a : Mu K n)
    (ha : IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) n) :
    IsPrimitiveRoot ((FieldPullback.muMap K L n a).toMul : (AlgebraicClosure L)ˣ) n := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  change IsPrimitiveRoot
    (algebraMap (AlgebraicClosure K) (AlgebraicClosure L)
      ((a.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) n
  exact (IsPrimitiveRoot.coe_units_iff.mpr ha).map_of_injective
    (algebraMap (AlgebraicClosure K) (AlgebraicClosure L)).injective

/-- Actual absolute-Galois restriction preserves the finite cyclotomic character.
The proof compares powers of the explicit image of P1's primitive root. -/
theorem character_restriction (g : Field.absoluteGaloisGroup L) :
    _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character K n
      (Field.absoluteGaloisGroup.mapOfAlgebra K L g) =
      _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character L n g := by
  let a := primitiveMu K n
  have ha := primitiveMu_spec K n
  have hb := IsPrimitiveRoot.coe_units_iff.mpr (muMap_primitive K n L a ha)
  apply Units.ext
  apply ZMod.val_injective
  apply hb.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  change (algebraMap (AlgebraicClosure K) (AlgebraicClosure L)
    ((a.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ^ _ = _
  rw [← map_pow, ← _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character_eval K n _ _
    (IsPrimitiveRoot.coe_units_iff.mpr ha).pow_eq_one,
    FieldPullback.restriction_commutes]
  exact _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character_eval L n g _ hb.pow_eq_one

omit [CharZero K] [CharZero L] [Algebra K L]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)] in
/-- The weight-one coordinate uses the same actual image root under extension. -/
theorem rootEquivZMod_baseChange (a : Mu K n)
    (ha : IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) n) (z : ZMod n) :
    FieldPullback.muMap K L n (rootEquivZMod K n a ha z) =
      rootEquivZMod L n (FieldPullback.muMap K L n a)
        (muMap_primitive K n L a ha) z := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  have hk : (k : ZMod n) = k • (1 : ZMod n) := by simp
  rw [hk, map_zsmul, map_zsmul, map_zsmul, rootEquivZMod_one, rootEquivZMod_one]

end FieldExtension
end Field.absoluteGaloisGroup.RootsOfUnity.CyclotomicCoordinates
