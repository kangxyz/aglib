/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Polynomial.LinearPlace
public import Aglib.KTheory.MilnorK.Norm.Polynomial.BaseChange

/-!
# The full norm branch sum at the original finite rational place

Linearizing a finite rational place preserves its residue field identically.
Applying coefficient base change to the norm therefore reduces its residue to
all actual branches over the linearized rational field. No branch is discarded,
and no norm-residue square or tower law is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {k : Type*} [Field k] [CharZero k]
variable (h : k[X]) [Fact (Irreducible h)]

local instance : Fact (Irreducible (X - C (AdjoinRoot.root h))) :=
  ⟨irreducible_X_sub_C _⟩

open scoped Classical in
/-- The original finite-place residue of a norm is the full sum of linear-place
residues of the actual coefficient-extended branch norms. -/
theorem residueAt_polynomialNorm_eq_linearPlace_sum
    (n : ℕ) (p : MonicIrreducible (RatFunc k))
    (x : K (AdjoinRoot p.val) (n + 1)) :
    residueAt h n (polynomialNorm (n + 1) p x) =
      ∑ q ∈ (placesAbove (fractionMap (algebraMap k (AdjoinRoot h))) p).attach,
        map n (linearRootEquiv (AdjoinRoot.root h)).toRingHom
          (residueAt (X - C (AdjoinRoot.root h)) n
            (polynomialNorm (n + 1) q.val
              (map (n + 1)
                (adjoinRootMap (fractionMap (algebraMap k (AdjoinRoot h))) p.val q.val.val
                  ((mem_placesAbove _ p q.val).mp q.property)) x))) := by
  rw [residueAt_eq_linearPlace h,
    polynomialNorm_restrict (fractionMap (algebraMap k (AdjoinRoot h)))]
  simp only [map_sum]

end MilnorK.PolynomialNorm
