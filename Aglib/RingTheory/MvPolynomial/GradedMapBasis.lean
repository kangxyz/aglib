/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.GradedMap
public import Aglib.RingTheory.MvPolynomial.CoordinatePieces

/-!
# The graded coefficient map on the monomial basis

For a ring map `σ : A →+* B`, the degree-`r` part `(gradedMap σ).gradedAddHom r : A[x]_r → B[x]_r`
of the graded coefficient map (`RingTheory/MvPolynomial/GradedMap`) sends the monomial basis
vector `x^a` of `homogeneousPieceBasis A r` (`RingTheory/MvPolynomial/CoordinatePieces`) to the
basis vector `x^a` of `homogeneousPieceBasis B r` (`gradedMap_homogeneousPieceBasis`). Consumer:
base change of the monomial map of projective space (`ProjectiveSpace/BaseChange/MonomialMap`).
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {ι A B : Type*} [CommRing A] [CommRing B]

/-- **The graded coefficient map preserves the monomial basis**: `σ` maps the basis vector `x^a`
of `A[x]_r` to the basis vector `x^a` of `B[x]_r`. -/
theorem gradedMap_homogeneousPieceBasis (σ : A →+* B) (r : ℕ)
    (a : {a : ι →₀ ℕ // a.degree = r}) :
    (gradedMap (ι := ι) σ).gradedAddHom r
        (homogeneousPieceBasis (ι := ι) A r a) =
      homogeneousPieceBasis (ι := ι) B r a := by
  apply Subtype.ext
  simp [homogeneousPieceBasis_val, MvPolynomial.map_monomial]

end MvPolynomial
