/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# A characteristic-zero DVR mapping to an arbitrary local ring

The inverse image of the target maximal ideal in the integers is prime. If
it is nonzero, localize there; otherwise localize at `(2)`. The resulting
actual integer localization is a characteristic-zero DVR and maps to the
original local ring. This map need not be local in residue characteristic
zero. No Noetherianity or characteristic hypothesis is placed on the target.
-/

@[expose] public noncomputable section

universe u

namespace Localization.IntegerLocalTarget

open IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The inverse image of the target maximal ideal in the integers. -/
abbrev residuePrime : Ideal ℤ := (maximalIdeal R).comap (Int.castRingHom R)

instance residuePrime_isPrime : (residuePrime R).IsPrime :=
  Ideal.comap_isPrime (Int.castRingHom R) _

/-- Select the actual nonzero integer prime, using `(2)` when the residue
characteristic is zero. -/
def prime : Ideal ℤ := by
  classical
  exact if residuePrime R = ⊥ then Ideal.span {(2 : ℤ)} else residuePrime R

instance prime_isPrime : (prime R).IsPrime := by
  classical
  unfold prime
  split_ifs
  · exact Ideal.isPrime_span_singleton_of_prime Int.prime_two
  · infer_instance

theorem prime_ne_bot : prime R ≠ ⊥ := by
  classical
  unfold prime
  split_ifs with h
  · intro hI
    exact (two_ne_zero : (2 : ℤ) ≠ 0) (Ideal.span_singleton_eq_bot.mp hI)
  · exact h

/-- Every denominator outside the selected prime has unit image in the target. -/
theorem residuePrime_le_prime : residuePrime R ≤ prime R := by
  classical
  unfold prime
  split_ifs with h
  · rw [h]
    exact bot_le
  · exact le_rfl

/-- The actual characteristic-zero coefficient DVR. -/
abbrev Ring := Localization.AtPrime (prime R)

instance : IsDiscreteValuationRing (Ring R) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    ℤ (prime_ne_bot R) (Ring R)

instance : CharZero (Ring R) :=
  charZero_of_injective_algebraMap
    (IsLocalization.injective (Ring R) (prime R).primeCompl_le_nonZeroDivisors)

/-- The canonical coefficient map. It is not asserted to be local. -/
def map : Ring R →+* R :=
  IsLocalization.lift (M := (prime R).primeCompl) (g := Int.castRingHom R)
    (fun s => notMem_maximalIdeal.mp
      (fun hs => s.property (residuePrime_le_prime R hs)))

theorem map_algebraMap (n : ℤ) :
    map R (algebraMap ℤ (Ring R) n) = n :=
  IsLocalization.lift_eq _ n

/-- The coefficient map restricts to the original integer map exactly. -/
theorem map_comp_algebraMap :
    (map R).comp (algebraMap ℤ (Ring R)) = Int.castRingHom R :=
  RingHom.ext (map_algebraMap R)

end Localization.IntegerLocalTarget
