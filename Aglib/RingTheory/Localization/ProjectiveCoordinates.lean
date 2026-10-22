/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Homogeneous coordinates on a principal open

A finite family in `A[1/f]` admits one common denominator, without a
nonzerodivisor, reducedness, or domain hypothesis. Adjoining that denominator
as coordinate zero gives an ideal whose restriction to the entire original
principal open is the unit ideal. These are algebraic inputs to prescribed-open
projective extension, not a claim of global resolution on an arbitrary open.
-/

@[expose] public section

namespace IsLocalization.Away

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable (f : A) [IsLocalization.Away f S]

/-- One denominator clears the original finite family, retaining each original
coordinate. This also applies to nonreduced rings and zerodivisor denominators. -/
theorem exists_common_power_coordinates {ι : Type*} [Finite ι] (s : ι → S) :
    ∃ (n : ℕ) (a : ι → A), ∀ i,
      s i * algebraMap A S f ^ n = algebraMap A S (a i) := by
  classical
  choose n a ha using fun i ↦ IsLocalization.Away.surj f (s i)
  let N : ℕ := ⨆ i, n i
  refine ⟨N, fun i ↦ a i * f ^ (N - n i), fun i ↦ ?_⟩
  have hn : n i ≤ N := le_ciSup (Finite.bddAbove_range _) i
  have hN : N = n i + (N - n i) := (Nat.add_sub_of_le hn).symm
  calc
    s i * algebraMap A S f ^ N =
        (s i * algebraMap A S f ^ n i) * algebraMap A S f ^ (N - n i) := by
          conv_lhs => rw [hN, pow_add]
          exact (mul_assoc _ _ _).symm
    _ = algebraMap A S (a i * f ^ (N - n i)) := by
      rw [ha i, map_mul, map_pow]

/-- The denominator is retained as the distinguished homogeneous coordinate. -/
def principalHomogeneousCoordinates {ι : Type*} (n : ℕ) (a : ι → A) : Option ι → A
  | none => f ^ n
  | some i => a i

/-- The actual coordinate ideal used for blowing up a principal-open family. -/
def principalCoordinateIdeal {ι : Type*} (n : ℕ) (a : ι → A) : Ideal A :=
  Ideal.span (Set.range (principalHomogeneousCoordinates f n a))

/-- The original denominator power belongs to the actual coordinate ideal. -/
theorem denominator_mem_principalCoordinateIdeal {ι : Type*} (n : ℕ) (a : ι → A) :
    f ^ n ∈ principalCoordinateIdeal f n a :=
  Ideal.subset_span ⟨none, rfl⟩

/-- Every original numerator belongs to the same coordinate ideal. -/
theorem numerator_mem_principalCoordinateIdeal {ι : Type*} (n : ℕ) (a : ι → A) (i : ι) :
    a i ∈ principalCoordinateIdeal f n a :=
  Ideal.subset_span ⟨some i, rfl⟩

/-- The coordinate ideal is the unit ideal after restriction to the original
principal open, not merely at a generic point. -/
theorem principalCoordinateIdeal_map_eq_top {ι : Type*} (n : ℕ) (a : ι → A) :
    (principalCoordinateIdeal f n a).map (algebraMap A S) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (denominator_mem_principalCoordinateIdeal f n a))
  rw [map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit f).pow n

/-- The complete homogeneous family is the original affine family with a
single common invertible scalar. In particular no coordinate is replaced by
another generating family. -/
theorem exists_principal_homogeneous_coordinates {ι : Type*} [Finite ι] (s : ι → S) :
    ∃ (n : ℕ) (a : ι → A),
      (∀ i, algebraMap A S (principalHomogeneousCoordinates f n a i) =
        algebraMap A S f ^ n * Option.elim i 1 s) ∧
      (principalCoordinateIdeal f n a).map (algebraMap A S) = ⊤ := by
  obtain ⟨n, a, ha⟩ := exists_common_power_coordinates f s
  refine ⟨n, a, ?_, principalCoordinateIdeal_map_eq_top f n a⟩
  intro i
  cases i with
  | none => simp [principalHomogeneousCoordinates]
  | some i => simpa [principalHomogeneousCoordinates, mul_comm] using (ha i).symm

end IsLocalization.Away
