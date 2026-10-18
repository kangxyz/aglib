/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.MonicIrreducible
public import Mathlib.RingTheory.LaurentSeries
public import Aglib.RingTheory.CompleteDVRExtension
public import Aglib.RingTheory.DVRRamificationDegree
public import Aglib.RingTheory.AdjoinRootCoefficientEquiv
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Constant root fields over the complete power-series DVR -/

@[expose] public noncomputable section

namespace PowerSeries.ConstantClosure

open Polynomial IsLocalRing

variable {k : Type*} [Field k]

/-- A constant monic irreducible polynomial remains irreducible over power series. -/
theorem irreducible_powerSeries (p : MonicIrreducible k) :
    Irreducible (p.val.map (algebraMap k (PowerSeries k))) := by
  apply (p.property.1.map _).irreducible_of_irreducible_map
    (φ := PowerSeries.constantCoeff) _
  have hc : PowerSeries.constantCoeff.comp (algebraMap k (PowerSeries k)) =
      RingHom.id k := by ext x; simp
  simpa only [Polynomial.map_map, hc, Polynomial.map_id] using p.property.2

/-- Gauss's lemma then gives the actual constant polynomial over Laurent series. -/
def constantPolynomial (p : MonicIrreducible k) : MonicIrreducible (LaurentSeries k) :=
  ⟨p.val.map (algebraMap k (LaurentSeries k)), p.property.1.map _, by
    have h := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
      (K := LaurentSeries k) (p.property.1.map (algebraMap k (PowerSeries k)))).mp
        (irreducible_powerSeries p)
    have hc : (algebraMap (PowerSeries k) (LaurentSeries k)).comp
        (algebraMap k (PowerSeries k)) = algebraMap k (LaurentSeries k) := rfl
    simpa only [map_map, hc] using h⟩

instance powerSeries_complete :
    IsAdicComplete (maximalIdeal (PowerSeries k)) (PowerSeries k) := by
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

/-- The root field of the constant polynomial over the Laurent-series field. -/
abbrev TopField (p : MonicIrreducible k) := AdjoinRoot (constantPolynomial p).val
/-- The integral closure of the power-series ring in the specified root field. -/
abbrev Closure (p : MonicIrreducible k) := integralClosure (PowerSeries k) (TopField p)

instance topField_finite (p : MonicIrreducible k) :
    FiniteDimensional (LaurentSeries k) (TopField p) :=
  (AdjoinRoot.powerBasis (constantPolynomial p).property.2.ne_zero).finite

variable [CharZero k]

instance laurent_charZero : CharZero (LaurentSeries k) :=
  charZero_of_injective_algebraMap (algebraMap k (LaurentSeries k)).injective

instance topField_charZero (p : MonicIrreducible k) : CharZero (TopField p) :=
  charZero_of_injective_algebraMap (algebraMap k (TopField p)).injective

instance closure_dvr (p : MonicIrreducible k) : IsDiscreteValuationRing (Closure p) :=
  IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing
    (PowerSeries k) (LaurentSeries k) (TopField p)

instance closure_fractionRing (p : MonicIrreducible k) : IsFractionRing (Closure p) (TopField p) :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (PowerSeries k) (LaurentSeries k) (TopField p) (Closure p)

instance closure_local (p : MonicIrreducible k) :
    IsLocalHom (algebraMap (PowerSeries k) (Closure p)) :=
  IsDiscreteValuationRing.CompleteExtension.integralClosure_isLocalHom
    (PowerSeries k) (LaurentSeries k) (TopField p)

/-- Every literal constant is integral over the power-series base. -/
theorem coefficient_integral (p : MonicIrreducible k) (x : AdjoinRoot p.val) :
    IsIntegral (PowerSeries k) (AdjoinRoot.coefficientMap (L := LaurentSeries k) p.val x) := by
  let : FiniteDimensional k (AdjoinRoot p.val) :=
    (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
  apply IsIntegral.map_of_comp_eq (algebraMap k (PowerSeries k))
    (AdjoinRoot.coefficientMap (L := LaurentSeries k) p.val).toRingHom
    _ (Algebra.IsIntegral.isIntegral (R := k) x)
  ext a
  exact ((AdjoinRoot.coefficientMap (L := LaurentSeries k) p.val).commutes a).symm

/-- Constants in the literal integral closure, not an abstract coefficient extension. -/
def constantMap (p : MonicIrreducible k) : AdjoinRoot p.val →+* Closure p :=
  (AdjoinRoot.coefficientMap (L := LaurentSeries k) p.val).toRingHom.codRestrict
    (integralClosure (PowerSeries k) (TopField p)).toSubring (coefficient_integral p)

theorem constantMap_apply (p : MonicIrreducible k) (x : AdjoinRoot p.val) :
    algebraMap (Closure p) (TopField p) (constantMap p x) =
      AdjoinRoot.coefficientMap (L := LaurentSeries k) p.val x := rfl

instance closure_finite (p : MonicIrreducible k) : Module.Finite (PowerSeries k) (Closure p) :=
  IsIntegralClosure.finite (PowerSeries k) (LaurentSeries k) (TopField p) (Closure p)

instance closure_torsionFree (p : MonicIrreducible k) :
    Module.IsTorsionFree (PowerSeries k) (Closure p) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (IsDiscreteValuationRing.CompleteExtension.integralClosure_algebraMap_injective
      (PowerSeries k) (LaurentSeries k) (TopField p))

instance closureCoefficientAlgebra (p : MonicIrreducible k) : Algebra k (Closure p) :=
  ((algebraMap (PowerSeries k) (Closure p)).comp (algebraMap k (PowerSeries k))).toAlgebra

instance closure_coefficientTower (p : MonicIrreducible k) :
    IsScalarTower k (PowerSeries k) (Closure p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The integral constant embedding fixes the original coefficient field. -/
theorem constantMap_algebraMap (p : MonicIrreducible k) (a : k) :
    constantMap p (algebraMap k (AdjoinRoot p.val) a) = algebraMap k (Closure p) a := by
  apply Subtype.ext
  change AdjoinRoot.coefficientMap (L := LaurentSeries k) p.val
    (algebraMap k (AdjoinRoot p.val) a) = _
  rw [AlgHom.commutes]
  rfl

/-- Reduction of the literal constants is an actual field embedding. -/
def residueEmbedding (p : MonicIrreducible k) :
    AdjoinRoot p.val →ₐ[k] ResidueField (Closure p) where
  __ := (residue (Closure p)).comp (constantMap p)
  commutes' a := by
    change residue (Closure p) (constantMap p (algebraMap k (AdjoinRoot p.val) a)) = _
    rw [constantMap_algebraMap]
    rfl

/-- The native residue equivalence of the base respects its coefficient algebra. -/
def baseResidueAlgEquiv : ResidueField (PowerSeries k) ≃ₐ[k] k where
  __ := PowerSeries.residueFieldOfPowerSeries
  commutes' a := by
    change PowerSeries.constantCoeff (PowerSeries.C a) = a
    simp

instance baseResidue_finite : Module.Finite k (ResidueField (PowerSeries k)) :=
  (baseResidueAlgEquiv (k := k)).symm.toLinearEquiv.finiteDimensional

instance closureResidue_finite (p : MonicIrreducible k) :
    Module.Finite k (ResidueField (Closure p)) :=
  Module.Finite.trans (ResidueField (PowerSeries k)) (ResidueField (Closure p))

theorem residue_finrank_eq (p : MonicIrreducible k) :
    Module.finrank k (ResidueField (Closure p)) =
      Module.finrank (ResidueField (PowerSeries k)) (ResidueField (Closure p)) := by
  have h := Module.finrank_mul_finrank k (ResidueField (PowerSeries k))
    (ResidueField (Closure p))
  have hb : Module.finrank k (ResidueField (PowerSeries k)) = 1 := by
    rw [(baseResidueAlgEquiv (k := k)).toLinearEquiv.finrank_eq, Module.finrank_self]
  simpa only [hb, one_mul] using h.symm

/-- The coefficient embedding fills the entire residue field, and the original
power-series parameter is already a uniformizer upstairs. -/
theorem degree_and_uniformizer (p : MonicIrreducible k) :
    Module.finrank k (ResidueField (Closure p)) = p.val.natDegree ∧
      Irreducible (algebraMap (PowerSeries k) (Closure p) PowerSeries.X) := by
  let : FiniteDimensional k (AdjoinRoot p.val) :=
    (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
  have hle : p.val.natDegree ≤ Module.finrank k (ResidueField (Closure p)) := by
    have h := (residueEmbedding p).toLinearMap.finrank_le_finrank_of_injective
      (residueEmbedding p).injective
    simpa only [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim] using h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Closure p)
  obtain ⟨e, hepos, u, he⟩ :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_exists_positive_ramification
      (PowerSeries k) (LaurentSeries k) (TopField p) PowerSeries.X_irreducible hϖ
  have hdegree := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    (PowerSeries k) (Closure p) (LaurentSeries k) (TopField p)
    PowerSeries.X_irreducible hϖ u e he
  have hd : Module.finrank (LaurentSeries k) (TopField p) = p.val.natDegree := by
    rw [(AdjoinRoot.powerBasis (constantPolynomial p).property.2.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
    exact Polynomial.natDegree_map _
  rw [hd, ← residue_finrank_eq] at hdegree
  have hfpos : 0 < Module.finrank k (ResidueField (Closure p)) := Module.finrank_pos
  have heone : e = 1 := by
    have hmul : e * Module.finrank k (ResidueField (Closure p)) ≤
        1 * Module.finrank k (ResidueField (Closure p)) := by
      simpa only [one_mul, ← hdegree] using hle
    have hele : e ≤ 1 := Nat.le_of_mul_le_mul_right hmul hfpos
    omega
  refine ⟨?_, ?_⟩
  · simpa only [heone, one_mul] using hdegree.symm
  · rw [he, heone, pow_one]
    exact (irreducible_units_mul u).mpr hϖ

/-- Exact residue equivalence induced by reduction of literal integral constants. -/
def residueEquiv (p : MonicIrreducible k) : AdjoinRoot p.val ≃+* ResidueField (Closure p) := by
  let : FiniteDimensional k (AdjoinRoot p.val) :=
    (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
  apply RingEquiv.ofBijective (residueEmbedding p).toRingHom
  refine ⟨(residueEmbedding p).injective, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (residueEmbedding p).toLinearMap) ?_).mp (residueEmbedding p).injective
  rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  exact (degree_and_uniformizer p).1.symm

@[simp]
theorem residueEquiv_apply (p : MonicIrreducible k) (x : AdjoinRoot p.val) :
    residueEquiv p x = residue (Closure p) (constantMap p x) := rfl

theorem uniformizer_irreducible (p : MonicIrreducible k) :
    Irreducible (algebraMap (PowerSeries k) (Closure p) PowerSeries.X) :=
  (degree_and_uniformizer p).2

/-- Coefficients agree with the original quotient map on the base residue field. -/
theorem residueEquiv_algebraMap (p : MonicIrreducible k) (a : k) :
    residueEquiv p (algebraMap k (AdjoinRoot p.val) a) =
      algebraMap (ResidueField (PowerSeries k)) (ResidueField (Closure p))
        (PowerSeries.residueFieldOfPowerSeries.symm a) := by
  have hbase : PowerSeries.residueFieldOfPowerSeries.symm a =
      residue (PowerSeries k) (PowerSeries.C a) := by
    apply PowerSeries.residueFieldOfPowerSeries.injective
    rw [RingEquiv.apply_symm_apply]
    change a = PowerSeries.constantCoeff (PowerSeries.C a)
    simp
  rw [residueEquiv_apply, constantMap_algebraMap, hbase, ResidueField.algebraMap_residue]
  rfl

/-- The residue equivalence is also linear over the literal coefficient field. -/
def residueAlgEquiv (p : MonicIrreducible k) :
    AdjoinRoot p.val ≃ₐ[k] ResidueField (Closure p) where
  __ := residueEquiv p
  commutes' := (residueEmbedding p).commutes

end PowerSeries.ConstantClosure
