/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.Basic
public import Aglib.KTheory.MilnorK.Residue.BaseChangeSupport

/-!
# Coefficient base change for all-degree polynomial-presentation norms

The restriction of an actual polynomial norm is the finite sum of polynomial
norms at the monic irreducible factors of its coefficient image. All summands
use the actual quotient-field maps, every input is an arbitrary Milnor class,
and degree zero is included. Characteristic zero makes each factor unramified.

The proof uses actual finite-residue surjectivity, the proved target support
and coordinate formulas, and the naturality of the actual infinity residue.
This establishes coefficient base change for the specified polynomial
presentations. It does not assert primitive-element independence, an
arbitrary finite-extension norm, or a norm tower law.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {k L : Type*} [Field k] [Field L]

/-- Total norms of actual residue vectors commute with coefficient restriction
in all degrees and all characteristics, by naturality at infinity. -/
theorem totalNorm_restrict_totalResidue (φ : k →+* L)
    (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    MilnorK.map n φ (totalNorm n (totalResidue n x)) =
      totalNorm n (totalResidue n (MilnorK.map (n + 1) (fractionMap φ) x)) := by
  rw [totalNorm_totalResidue, totalNorm_totalResidue,
    InfinityResidue.residue_restrict, map_neg]

open scoped Classical in
/-- Coefficient restriction of a polynomial-presentation norm is the actual
finite sum over all target factors, on every class in every degree. -/
theorem polynomialNorm_restrict [CharZero k]
    (φ : k →+* L) (n : ℕ) (p : MonicIrreducible k) (z : K (AdjoinRoot p.val) n) :
    MilnorK.map n φ (polynomialNorm n p z) =
      ∑ q ∈ (placesAbove φ p).attach,
        polynomialNorm n q.val
          (MilnorK.map n (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)) z) := by
  classical
  obtain ⟨x, hx⟩ := totalResidue_surjective n (DFinsupp.single p z)
  let y := totalResidue n (MilnorK.map (n + 1) (fractionMap φ) x)
  have hy : y.support ⊆ placesAbove φ p :=
    totalResidue_restrict_single_support_subset φ n p z x hx
  calc
    MilnorK.map n φ (polynomialNorm n p z) = totalNorm n y := by
      rw [← totalNorm_single, ← hx]
      exact totalNorm_restrict_totalResidue φ n x
    _ = ∑ q ∈ y.support, polynomialNorm n q (y q) := totalNorm_eq_sum n y
    _ = ∑ q ∈ placesAbove φ p, polynomialNorm n q (y q) := by
      apply Finset.sum_subset hy
      intro q _ hq
      rw [DFinsupp.notMem_support_iff.mp hq, map_zero]
    _ = ∑ q ∈ (placesAbove φ p).attach, polynomialNorm n q.val (y q.val) :=
      (Finset.sum_attach (placesAbove φ p) (fun q => polynomialNorm n q (y q))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      exact totalResidue_restrict_single_of_dvd φ n p z x hx q.val
        ((mem_placesAbove φ p q.val).mp q.property)

open scoped Classical in
/-- The same finite-factor formula as an equality of integer-linear maps. -/
theorem polynomialNorm_comp_restrict [CharZero k]
    (φ : k →+* L) (n : ℕ) (p : MonicIrreducible k) :
    (MilnorK.map n φ).comp (polynomialNorm n p) =
      ∑ q ∈ (placesAbove φ p).attach,
        (polynomialNorm n q.val).comp
          (MilnorK.map n (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property))) := by
  apply LinearMap.ext
  intro z
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using
    polynomialNorm_restrict φ n p z

end MilnorK.PolynomialNorm
