/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialNorm
public import Aglib.KTheory.MilnorK.K3.ResidueBaseChangeSupport

/-!
# Coefficient base change for the actual polynomial Milnor K₂ norms

The restriction of a polynomial-presentation norm is the finite sum of the
norms at the monic irreducible factors of the coefficient image. Every summand
uses the literal quotient-field map `adjoinRootMap` and the original Milnor K₂
groups, with their original integer scalars.

The proof lifts a single actual finite residue by proved surjectivity, uses
the proved target support and coordinate formulas, and compares the two actual
infinity residues. Characteristic zero is explicit; no compatibility record,
primitive-element independence, or arbitrary-extension norm is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {k L : Type*} [Field k] [Field L]

/-- The actual total norm commutes with restriction on actual finite residue
vectors coming from a rational-function Milnor K₃ class. -/
theorem totalNorm_restrict_totalResidue [CharZero k]
    (φ : k →+* L) (x : Group (RatFunc k)) :
    MilnorK.K2.map φ (totalNorm (totalResidue x)) =
      totalNorm (totalResidue (MilnorK.K3.map (fractionMap φ) x)) := by
  rw [totalNorm_totalResidue, totalNorm_totalResidue,
    InfinityResidue.residue_restrict, map_neg]

open scoped Classical in
/-- Restriction of the actual polynomial norm is the genuine finite sum over
all monic irreducible factors after coefficient extension. The membership
proof supplies exactly the divisibility needed for the literal quotient map. -/
theorem polynomialNorm_restrict [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) (z : MilnorK.K2.Group (AdjoinRoot p.val)) :
    MilnorK.K2.map φ (polynomialNorm p z) =
      ∑ q ∈ (placesAbove φ p).attach,
        polynomialNorm q.val
          (MilnorK.K2.map (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)) z) := by
  classical
  obtain ⟨x, hx⟩ := totalResidue_surjective (DFinsupp.single p z)
  let y := totalResidue (MilnorK.K3.map (fractionMap φ) x)
  have hy : y.support ⊆ placesAbove φ p :=
    totalResidue_restrict_single_support_subset φ p z x hx
  calc
    MilnorK.K2.map φ (polynomialNorm p z) = totalNorm y := by
      rw [← totalNorm_single, ← hx]
      exact totalNorm_restrict_totalResidue φ x
    _ = ∑ q ∈ y.support, polynomialNorm q (y q) := totalNorm_eq_sum y
    _ = ∑ q ∈ placesAbove φ p, polynomialNorm q (y q) := by
      apply Finset.sum_subset hy
      intro q _ hq
      rw [DFinsupp.notMem_support_iff.mp hq, map_zero]
    _ = ∑ q ∈ (placesAbove φ p).attach, polynomialNorm q.val (y q.val) :=
      (Finset.sum_attach (placesAbove φ p) (fun q => polynomialNorm q (y q))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      exact totalResidue_restrict_single_of_dvd φ p z x hx q.val
        ((mem_placesAbove φ p q.val).mp q.property)

open scoped Classical in
/-- The same finite factor formula as equality of integer-linear maps between
the original polynomial residue-field and coefficient-field Milnor K₂ groups. -/
theorem polynomialNorm_comp_restrict [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) :
    (MilnorK.K2.map φ).comp (polynomialNorm p) =
      ∑ q ∈ (placesAbove φ p).attach,
        (polynomialNorm q.val).comp
          (MilnorK.K2.map (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property))) := by
  apply LinearMap.ext
  intro z
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using
    polynomialNorm_restrict φ p z

end MilnorK.K3.PolynomialNorm
