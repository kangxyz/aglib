/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.RationalExactness
public import Aglib.KTheory.MilnorK.K3.InfinityDegree

/-!
# Polynomial-presentation norms on the original Milnor K₂ groups

The negative actual infinity residue descends through the quotient by the
constant Milnor K₃ image. The proved rational residue exactness identifies that
quotient with the dependent finite sum of original finite-place Milnor K₂
groups. Its components give the polynomial-presentation norms and actual
finite-rational reciprocity. Their composite with the constant-field K₂ map
is multiplication by the polynomial degree.

No norm interface or injectivity of constant Milnor K₃ is assumed. This file
does not assert independence from a primitive element or polynomial
presentation, arbitrary extension towers, or motivic compatibility.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.PolynomialNorm

open Polynomial PolynomialResidue

variable {k : Type*} [Field k]

/-- The negative infinity residue kills the entire constant-image submodule. -/
theorem constant_range_le_ker_neg_infinity :
    LinearMap.range (MilnorK.K3.map (RatFunc.C : k →+* RatFunc k)) ≤
      LinearMap.ker (-InfinityResidue.residue k) := by
  rintro _ ⟨x, rfl⟩
  change -InfinityResidue.residue k (MilnorK.K3.map RatFunc.C x) = 0
  rw [InfinityResidue.residue_constants, neg_zero]

/-- The actual negative infinity residue descended by its proved vanishing. -/
def quotientNorm :
    (Group (RatFunc k) ⧸ LinearMap.range (MilnorK.K3.map (RatFunc.C : k →+* RatFunc k)))
      →ₗ[ℤ] MilnorK.K2.Group k :=
  (LinearMap.range (MilnorK.K3.map (RatFunc.C : k →+* RatFunc k))).liftQ
    (-InfinityResidue.residue k) constant_range_le_ker_neg_infinity

@[simp] theorem quotientNorm_mk (x : Group (RatFunc k)) :
    quotientNorm (Submodule.Quotient.mk x) = -InfinityResidue.residue k x := rfl

/-- The actual total norm on the original dependent finite residue vector. -/
def totalNorm :
    (Π₀ p : MonicIrreducible k, MilnorK.K2.Group (AdjoinRoot p.val)) →ₗ[ℤ] MilnorK.K2.Group k :=
  quotientNorm.comp (quotientConstantEquivResidues.symm.toLinearMap)

/-- The constructed total norm computes minus the actual infinity residue. -/
@[simp] theorem totalNorm_totalResidue (x : Group (RatFunc k)) :
    totalNorm (totalResidue x) = -InfinityResidue.residue k x := by
  rw [← quotientConstantEquivResidues_mk x]
  simp only [totalNorm, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, quotientNorm_mk]

/-- The actual rational-function identity as an equality of linear maps. -/
theorem totalNorm_comp_totalResidue :
    (totalNorm (k := k)).comp totalResidue = -InfinityResidue.residue k := by
  apply LinearMap.ext
  intro x
  exact totalNorm_totalResidue x

/-- Surjectivity of actual finite residues makes this total norm unique. -/
theorem totalNorm_unique
    (f : (Π₀ p : MonicIrreducible k, MilnorK.K2.Group (AdjoinRoot p.val)) →ₗ[ℤ] MilnorK.K2.Group k)
    (hf : ∀ x : Group (RatFunc k), f (totalResidue x) = -InfinityResidue.residue k x) :
    f = totalNorm := by
  ext y
  obtain ⟨x, rfl⟩ := totalResidue_surjective y
  exact (hf x).trans (totalNorm_totalResidue x).symm

/-- The actual norm for a literal monic irreducible polynomial presentation. -/
def polynomialNorm (p : MonicIrreducible k) :
    MilnorK.K2.Group (AdjoinRoot p.val) →ₗ[ℤ] MilnorK.K2.Group k := by
  classical
  exact totalNorm.comp (DFinsupp.lsingle (R := ℤ)
    (M := fun q : MonicIrreducible k => MilnorK.K2.Group (AdjoinRoot q.val)) p)

@[simp] theorem totalNorm_single [DecidableEq (MonicIrreducible k)]
    (p : MonicIrreducible k) (x : MilnorK.K2.Group (AdjoinRoot p.val)) :
    totalNorm (DFinsupp.single p x) = polynomialNorm p x := by
  simp only [polynomialNorm, LinearMap.comp_apply, DFinsupp.lsingle_apply]
  congr 1
  apply DFinsupp.ext
  intro q
  by_cases h : q = p
  · subst q
    simp only [DFinsupp.single_eq_same]
  · simp only [DFinsupp.single_apply]

/-- Summing the actual polynomial norms recovers the total norm. -/
theorem lsum_polynomialNorm [DecidableEq (MonicIrreducible k)] :
    DFinsupp.lsum ℤ (polynomialNorm (k := k)) = totalNorm := by
  apply DFinsupp.lhom_ext
  intro p x
  rw [DFinsupp.lsum_single, totalNorm_single]

open scoped Classical in
/-- The total norm is the finite sum over the genuine support of its input. -/
theorem totalNorm_eq_sum
    (y : Π₀ p : MonicIrreducible k, MilnorK.K2.Group (AdjoinRoot p.val)) :
    totalNorm y = ∑ p ∈ y.support, polynomialNorm p (y p) := by
  rw [← lsum_polynomialNorm]
  simp only [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    LinearMap.toAddMonoidHom_coe, DFinsupp.sum]

open scoped Classical in
/-- Actual finite-rational reciprocity in the original base-field Milnor K₂. -/
theorem finite_rational_reciprocity (x : Group (RatFunc k)) :
    (∑ p ∈ (totalResidue x).support, polynomialNorm p (residueAt p.val x)) +
      InfinityResidue.residue k x = 0 := by
  change (∑ p ∈ (totalResidue x).support, polynomialNorm p (totalResidue x p)) + _ = 0
  rw [← totalNorm_eq_sum, totalNorm_totalResidue, neg_add_cancel]

/-- Distinct monic irreducible polynomials cannot divide one another. -/
theorem not_dvd_of_ne (p q : MonicIrreducible k) (hpq : p ≠ q) : ¬ q.val ∣ p.val := by
  intro h
  apply hpq
  apply Subtype.ext
  exact eq_of_monic_of_associated p.property.1 q.property.1
    (q.property.2.associated_of_dvd p.property.2 h).symm

/-- Every finite place is prime to a nonzero constant polynomial. -/
theorem not_dvd_constant (p : MonicIrreducible k) (a : kˣ) : ¬ p.val ∣ C (a : k) :=
  p.property.1.not_dvd_of_natDegree_lt (C_ne_zero.mpr a.ne_zero)
    (by simpa only [natDegree_C] using p.property.2.natDegree_pos)

/-- Reduction of a constant polynomial unit is the original constant-field unit map. -/
theorem quotientUnit_constant (p : MonicIrreducible k) (a : kˣ) :
    quotientUnit p.val (C (a : k)) (not_dvd_constant p a) =
      Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom a := by
  apply Units.ext
  rfl

/-- A polynomial and two constants have just the one actual finite residue. -/
theorem totalResidue_polynomial_constants [DecidableEq (MonicIrreducible k)]
    (p : MonicIrreducible k) (a b : kˣ) :
    totalResidue (symbol3 (polynomialUnit p.val p.property.2.ne_zero)
      (InfinityResidue.constantUnit k a) (InfinityResidue.constantUnit k b)) =
      DFinsupp.single p
        (MilnorK.K2.map (algebraMap k (AdjoinRoot p.val)) (MilnorK.K2.symbol a b)) := by
  classical
  apply DFinsupp.ext
  intro q
  rw [totalResidue_apply, ← InfinityResidue.polynomialUnit_constant k a,
    ← InfinityResidue.polynomialUnit_constant k b]
  by_cases hpq : p = q
  · subst q
    rw [DFinsupp.single_eq_same, residueAt_polynomial_units _ _ _ _ _
      (not_dvd_constant p a) (not_dvd_constant p b), MilnorK.K2.map_symbol,
      quotientUnit_constant, quotientUnit_constant]
  · rw [DFinsupp.single_eq_of_ne (Ne.symm hpq)]
    exact residueAt_polynomial_units_zero q.val _ _ _ _ _ _
      (not_dvd_of_ne p q hpq) (not_dvd_constant q a) (not_dvd_constant q b)

/-- The polynomial norm has its actual positive degree on constant K₂ symbols. -/
theorem polynomialNorm_map_constant_symbol (p : MonicIrreducible k) (a b : kˣ) :
    polynomialNorm p
      (MilnorK.K2.map (algebraMap k (AdjoinRoot p.val)) (MilnorK.K2.symbol a b)) =
      (p.val.natDegree : ℤ) • MilnorK.K2.symbol a b := by
  classical
  rw [← totalNorm_single, ← totalResidue_polynomial_constants,
    totalNorm_totalResidue, InfinityResidue.residue_polynomial_constants]
  simp only [neg_smul, neg_neg]

/-- On the entire original constant K₂ image the norm is multiplication by degree. -/
theorem polynomialNorm_comp_constants (p : MonicIrreducible k) :
    (polynomialNorm p).comp (MilnorK.K2.map (algebraMap k (AdjoinRoot p.val))) =
      (p.val.natDegree : ℤ) • LinearMap.id := by
  apply MilnorK.K2.linearMap_ext
  intro a b
  exact polynomialNorm_map_constant_symbol p a b

/-- The degree formula applies to every original base-field Milnor K₂ class. -/
theorem polynomialNorm_map_constants (p : MonicIrreducible k) (x : MilnorK.K2.Group k) :
    polynomialNorm p (MilnorK.K2.map (algebraMap k (AdjoinRoot p.val)) x) =
      (p.val.natDegree : ℤ) • x :=
  LinearMap.congr_fun (polynomialNorm_comp_constants p) x

end MilnorK.K3.PolynomialNorm
