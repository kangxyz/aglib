/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.PrimitiveCoordinates
public import Aglib.RingTheory.RootsOfUnity.Inclusion
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Primitive roots and positive-level root cardinality

The characteristic-zero existence and cardinality results keep positive levels;
the power-map primitivity results use their weaker original hypotheses.
-/

@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity.Exactness
open Field.absoluteGaloisGroup.RootsOfUnity
  Field.absoluteGaloisGroup.RootsOfUnity.PrimitiveCoordinates
  Field.absoluteGaloisGroup.RootsOfUnity.Reduction
universe u
variable (K : Type u) [Field K] [CharZero K]
/-- A primitive generator exists in the actual algebraic closure at every positive level. -/
theorem exists_primitiveMu (n : ℕ) [NeZero n] :
    ∃ a : Mu K n, IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) n
  refine ⟨Additive.ofMul hζ.toRootsOfUnity, ?_⟩
  apply IsPrimitiveRoot.coe_units_iff.mp
  change IsPrimitiveRoot ((hζ.toRootsOfUnity : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) n
  simpa only [IsPrimitiveRoot.val_toRootsOfUnity_coe] using hζ

/-- The cardinality of the actual root group is n. -/
theorem mu_card (n : ℕ) [NeZero n] : Nat.card (Mu K n) = n := by
  obtain ⟨a, ha⟩ := exists_primitiveMu K n
  rw [← Nat.card_congr (rootEquivZMod K n a ha).toEquiv, Nat.card_zmod]

variable (a b : ℕ)
/-- The corresponding actual root power map. -/
def tailMuReduction : Mu K (a * b) →ₗ[ℤ] Mu K b :=
  (muReduction K b a).comp (muCast K (Nat.mul_comm a b))

omit [CharZero K] in
theorem muReduction_primitive (hb : 0 < b) (x : Mu K (a * b))
    (hx : IsPrimitiveRoot (x.toMul : (AlgebraicClosure K)ˣ) (a * b)) :
    IsPrimitiveRoot ((muReduction K a b x).toMul : (AlgebraicClosure K)ˣ) a := by
  change IsPrimitiveRoot ((x.toMul : (AlgebraicClosure K)ˣ) ^ b) a
  simpa only [Nat.mul_div_cancel a hb] using
    hx.pow_of_dvd (Nat.ne_of_gt hb) (dvd_mul_left b a)

omit [CharZero K] in
theorem tailMuReduction_primitive (ha : 0 < a) (x : Mu K (a * b))
    (hx : IsPrimitiveRoot (x.toMul : (AlgebraicClosure K)ˣ) (a * b)) :
    IsPrimitiveRoot ((tailMuReduction K a b x).toMul : (AlgebraicClosure K)ˣ) b := by
  have h := hx.pow_of_dvd (Nat.ne_of_gt ha) (dvd_mul_right a b)
  simpa only [tailMuReduction, LinearMap.comp_apply, muReduction_value, muCast_value,
    Nat.mul_div_cancel_left b ha] using h

end Field.absoluteGaloisGroup.RootsOfUnity.Exactness
