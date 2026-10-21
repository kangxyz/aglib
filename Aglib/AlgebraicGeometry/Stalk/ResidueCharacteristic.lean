/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne
public import Mathlib.Algebra.CharP.Basic

/-!
# Units away from the actual residue characteristic

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.ResidueCharacteristic`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `e6552a5a96ebb464122c01fab666ceff07e0c60ad83d8fae4c3f1cce561d484b`, selected lines [[23,
39]].
The actual scheme objects, canonical maps, universes and conditions are retained.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.CodimensionOnePoint
variable {X : Scheme.{u}}

/-- A prime is a unit in the actual local ring when the actual residue characteristic differs. -/
theorem prime_isUnit_of_residueChar_ne (p : ℕ) [Fact p.Prime]
    (x : CodimensionOnePoint X) (haway : ringChar x.residueField ≠ p) :
    IsUnit (p : x.localRing) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (p : x.localRing)).mp
  rw [map_natCast]
  exact fun hp => haway (CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hp)

/-- A prime-power level is a unit at each indexed stalk away from its residue characteristic. -/
theorem level_isUnit_of_residueChar_ne (n p : ℕ) [Fact p.Prime]
    (r : ℕ) (hlevel : n = p ^ r) (x : CodimensionOnePoint X)
    (haway : ringChar x.residueField ≠ p) : IsUnit (n : x.localRing) := by
  rw [hlevel, Nat.cast_pow]
  exact (prime_isUnit_of_residueChar_ne p x haway).pow r

end AlgebraicGeometry.Scheme.CodimensionOnePoint
