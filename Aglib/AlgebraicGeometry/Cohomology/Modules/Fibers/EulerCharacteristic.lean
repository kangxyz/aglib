/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Fibers
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# The Euler characteristic of original fibre cohomology

This is the alternating sum of the original cohomology dimensions of the
ordinary pulled coefficient on the actual residue-field fibre. A proved
cohomological vanishing bound identifies it with the corresponding finite
sum. Its definition is independent of a projective embedding or a chosen
complex. Geometric finiteness and local constancy are supplied downstream.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The alternating sum of the original dimensions of the actual fibre cohomology.
As for the native complex Euler characteristic, `finsum` is zero when its support is
infinite; geometric applications supply an actual vanishing bound. -/
def moduleFiberEulerChar (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
    (p : PrimeSpectrum R) : ℤ :=
  ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * (moduleFiberCohomologyDimension f M q p : ℤ)

/-- A genuine vanishing bound computes the original fibre Euler characteristic by
the finite alternating sum in the same natural degrees. -/
theorem moduleFiberEulerChar_eq_sum_range (f : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (p : PrimeSpectrum R) (n : ℕ)
    (hvan : ∀ q, n < q → moduleFiberCohomologyDimension f M q p = 0) :
    moduleFiberEulerChar f M p = ∑ q ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ q * (moduleFiberCohomologyDimension f M q p : ℤ) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro q hq
  by_contra h
  have hn : n < q := by
    have : ¬q < n + 1 := by simpa only [Finset.mem_coe, Finset.mem_range] using h
    omega
  exact hq (by simp only [hvan q hn, Nat.cast_zero, mul_zero])

end AlgebraicGeometry.Scheme.Cohomology
