/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Three generators at a nonregular local surface

The native regularity criterion excludes at most two maximal-ideal generators
in dimension two. An actual bound of three therefore gives cotangent rank
three, for the original residue-field action. No domain, normality,
Gorensteinness, rationality or Hilbert-function hypothesis is needed.
-/

@[expose] public section

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A nonregular Noetherian local surface with at most three maximal-ideal
generators has actual cotangent dimension three. -/
theorem cotangent_finrank_eq_three_of_spanFinrank_le_three
    (hd : ringKrullDim R = 2) (hsing : ¬ IsRegularLocalRing R)
    (hgen : (maximalIdeal R).spanFinrank ≤ 3) :
    Module.finrank (ResidueField R) (CotangentSpace R) = 3 := by
  have hgt : 2 < (maximalIdeal R).spanFinrank := by
    by_contra h
    have hle : (maximalIdeal R).spanFinrank ≤ 2 := by omega
    apply hsing
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le R
    rw [hd]
    exact_mod_cast hle
  have hdim : (maximalIdeal R).spanFinrank = 3 := by omega
  exact (spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R).symm.trans hdim

/-- Three literal generators of the original maximal ideal give cotangent
rank three when the dimension-two local ring is nonregular. -/
theorem cotangent_finrank_eq_three_of_maximalIdeal_span_triple
    (hd : ringKrullDim R = 2) (hsing : ¬ IsRegularLocalRing R) (p u v : R)
    (hgen : maximalIdeal R = Ideal.span ({p, u, v} : Set R)) :
    Module.finrank (ResidueField R) (CotangentSpace R) = 3 := by
  apply cotangent_finrank_eq_three_of_spanFinrank_le_three hd hsing
  rw [hgen]
  apply (Submodule.spanFinrank_span_le_ncard_of_finite
    (((Set.finite_singleton v).insert u).insert p)).trans
  have hpair : ({u, v} : Set R).ncard ≤ 2 := by
    simpa only [Set.ncard_singleton] using Set.ncard_insert_le u ({v} : Set R)
  have htriple := Set.ncard_insert_le p ({u, v} : Set R)
  omega

end IsLocalRing
