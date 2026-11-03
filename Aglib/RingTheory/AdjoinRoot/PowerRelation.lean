/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.IsAdjoinRoot

/-!
# A monic power-relation presentation of a specified generator

An integral generator of a torsion-free domain algebra over a normal domain
has its native minimal-polynomial presentation. A power relation whose degree
is the original module finrank identifies that same presentation with the
power-relation polynomial. The forward map and root remain the originals.
-/

@[expose] public noncomputable section

open Polynomial

namespace IsAdjoinRootMonic

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [Algebra A B] [Module.IsTorsionFree A B]

/-- Present the original algebra using its specified generator and power
relation. Integrality follows from that same positive power relation. No prime
degree, characteristic or local-ring premise is used. -/
def ofPowerRelation {p : ℕ} (hp : p ≠ 0) (hdegree : Module.finrank A B = p)
    (z : B) (a : A) (hpow : algebraMap A B a = z ^ p)
    (hgen : Algebra.adjoin A {z} = ⊤) :
    IsAdjoinRootMonic B ((X : A[X]) ^ p - C a) := by
  have hz : IsIntegral A z := by
    apply IsIntegral.of_pow (Nat.pos_of_ne_zero hp)
    rw [← hpow]
    exact isIntegral_algebraMap
  let h₀ := IsAdjoinRootMonic.mkOfAdjoinEqTop hz hgen
  have hdegree' : (minpoly A z).natDegree = p := h₀.finrank.symm.trans hdegree
  have hzero : aeval z ((X : A[X]) ^ p - C a) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, ← hpow, sub_self]
  have hdiv : minpoly A z ∣ (X : A[X]) ^ p - C a :=
    (minpoly.isIntegrallyClosed_dvd_iff hz _).mp hzero
  have heq : (X : A[X]) ^ p - C a = minpoly A z :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hz)
      (Polynomial.monic_X_pow_sub_C a hp) hdiv
      (by simpa only [Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow, hdegree']
        using (le_refl p))
  exact
    { map := aeval z
      map_surjective := h₀.map_surjective
      ker_map := by rw [heq]; exact h₀.ker_map
      monic := Polynomial.monic_X_pow_sub_C a hp }

@[simp]
theorem ofPowerRelation_root {p : ℕ} (hp : p ≠ 0) (hdegree : Module.finrank A B = p)
    (z : B) (a : A) (hpow : algebraMap A B a = z ^ p)
    (hgen : Algebra.adjoin A {z} = ⊤) :
    (ofPowerRelation hp hdegree z a hpow hgen).root = z :=
  aeval_X z

@[simp]
theorem ofPowerRelation_map {p : ℕ} (hp : p ≠ 0) (hdegree : Module.finrank A B = p)
    (z : B) (a : A) (hpow : algebraMap A B a = z ^ p)
    (hgen : Algebra.adjoin A {z} = ⊤) :
    (ofPowerRelation hp hdegree z a hpow hgen).map = aeval z := rfl

end IsAdjoinRootMonic
