/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.AbsoluteIrreducibilitySpreading
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Data.Finsupp.Fintype

/-! # Principal spreading of absolute polynomial irreducibility

Every nontrivial factorization of the original polynomial has bounded degree,
and hence gives a point of one of the original finite coefficient algebras.
Generic emptiness of these finitely many algebras supplies one nonzero scalar
excluding every factorization after every field specialization. A preserved
positive-degree coefficient also excludes zero and unit specializations.
-/

@[expose] public noncomputable section

namespace MvPolynomial.FactorizationAlgebra

variable {σ : Type*} [Finite σ]

/-- Original exponent vectors with a uniform coordinate bound. -/
abbrev BoundedMonomial (σ : Type*) (d : ℕ) := {e : σ →₀ ℕ // ∀ s, e s ≤ d}

instance (d : ℕ) : Finite (BoundedMonomial σ d) := by
  apply Finite.of_injective (fun e : BoundedMonomial σ d =>
    fun s => (⟨e.val s, Nat.lt_succ_of_le (e.property s)⟩ : Fin (d + 1)))
  intro e f h
  apply Subtype.ext
  ext s
  exact congrArg Fin.val (congrFun h s)

instance (d : ℕ) : Fintype (BoundedMonomial σ d) := Fintype.ofFinite _

omit [Finite σ] in
/-- The finite polynomial constructor recovers each original coefficient when
its monomial family is injective. -/
theorem coeff_polynomial_of_injective {ι S : Type*} [Fintype ι] [CommRing S]
    (m : ι → σ →₀ ℕ) (hm : Function.Injective m) (a : ι → S) (i : ι) :
    (polynomial m a).coeff (m i) = a i := by
  classical
  simp only [polynomial, coeff_sum, coeff_monomial, hm.eq_iff]
  simp

/-- The actual bounded coefficient expansion of a polynomial of bounded total degree. -/
theorem polynomial_bounded_coeff {S : Type*} [CommRing S]
    (Q : MvPolynomial σ S) (d : ℕ) (hQ : Q.totalDegree ≤ d) :
    polynomial (fun e : BoundedMonomial σ d => e.val) (fun e => Q.coeff e.val) = Q := by
  classical
  ext e
  by_cases he : ∀ s, e s ≤ d
  · exact coeff_polynomial_of_injective _ Subtype.val_injective _ ⟨e, he⟩
  · have hcoeff : Q.coeff e = 0 := by
      by_contra hc
      have hs : e ∈ Q.support := mem_support_iff.mpr hc
      exact he (fun s => (monomial_le_degreeOf s hs).trans
        ((degreeOf_le_totalDegree Q s).trans hQ))
    rw [hcoeff]
    simp only [polynomial, coeff_sum, coeff_monomial]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : i.val ≠ e := fun h => he (h ▸ i.property)
    simp only [hne, ↓reduceIte]

omit [Finite σ] in
/-- A nonzero coefficient of a nonconstant monomial excludes units. -/
theorem not_isUnit_of_nonconstant_coeff {L : Type*} [Field L]
    {Q : MvPolynomial σ L} {e : σ →₀ ℕ} (he : e ≠ 0) (hc : Q.coeff e ≠ 0) :
    ¬ IsUnit Q := by
  intro h
  have hC := totalDegree_eq_zero_iff_eq_C.mp (isUnit_iff_totalDegree_of_isReduced.mp h).2
  have heq := congrArg (fun P : MvPolynomial σ L => P.coeff e) hC
  have hz : (C (Q.coeff 0) : MvPolynomial σ L).coeff e = 0 := by
    exact coeff_C_of_ne_zero he _
  exact hc (heq.trans hz)

omit [Finite σ] in
/-- A nonzero nonunit over a field has an actual nonconstant nonzero coefficient. -/
theorem exists_nonconstant_coeff {L : Type*} [Field L]
    (Q : MvPolynomial σ L) (hQ : Q ≠ 0) (hu : ¬ IsUnit Q) :
    ∃ e : σ →₀ ℕ, e ≠ 0 ∧ Q.coeff e ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hC : Q = C (Q.coeff 0) := by
    ext e
    by_cases he : e = 0
    · subst e
      simp only [coeff_C, ↓reduceIte]
    · simp only [coeff_C, Ne.symm he, ↓reduceIte, h e he]
  have hc : Q.coeff 0 ≠ 0 := by
    intro hc
    exact hQ (by simpa only [hc, map_zero] using hC)
  exact hu (hC.symm ▸ hc.isUnit.map C)

/-- Absolute irreducibility excludes every actual bounded factorization chart
whose two inverted coefficients have nonzero exponents. -/
theorem isEmpty_bounded_factorization_of_irreducible
    {R Ω : Type*} [CommRing R] [Field Ω] [_root_.Algebra R Ω]
    (P : MvPolynomial σ R) (d : ℕ) (i j : BoundedMonomial σ d)
    (hi : i.val ≠ 0) (hj : j.val ≠ 0)
    (hP : Irreducible (map (algebraMap R Ω) P)) :
    IsEmpty (Algebra P (fun e : BoundedMonomial σ d => e.val) i j →ₐ[R] Ω) := by
  constructor
  intro f
  obtain ⟨a, b, u, v, hfac, hai, hbj⟩ := (nonempty_algHom_iff P _ i j).mp ⟨f⟩
  have ha : a i ≠ 0 := by
    intro h
    exact zero_ne_one (by simpa only [h, mul_zero] using hai)
  have hb : b j ≠ 0 := by
    intro h
    exact zero_ne_one (by simpa only [h, mul_zero] using hbj)
  rcases hP.isUnit_or_isUnit hfac with h | h
  · exact not_isUnit_of_nonconstant_coeff hi
      (by simpa only [coeff_polynomial_of_injective _ Subtype.val_injective] using ha) h
  · exact not_isUnit_of_nonconstant_coeff hj
      (by simpa only [coeff_polynomial_of_injective _ Subtype.val_injective] using hb) h

/-- A polynomial irreducible over an algebraically closed extension of the
fraction field stays irreducible under every field specialization on one
nonzero principal open of the original domain. -/
theorem exists_ne_zero_forall_irreducible_map
    (R K Ω : Type*) [CommRing R] [IsDomain R] [Field K] [_root_.Algebra R K]
    [IsFractionRing R K] [Field Ω] [_root_.Algebra K Ω] [_root_.Algebra R Ω]
    [IsScalarTower R K Ω] [IsAlgClosed Ω]
    (P : MvPolynomial σ R) (hP : Irreducible (map (algebraMap R Ω) P)) :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type*) [Field L] (φ : R →+* L),
      φ r ≠ 0 → Irreducible (map φ P) := by
  classical
  let I := {i : BoundedMonomial σ P.totalDegree // i.val ≠ 0}
  let : Fintype I := Fintype.ofFinite I
  have hempty (ij : I × I) := isEmpty_bounded_factorization_of_irreducible
    P P.totalDegree ij.1.val ij.2.val ij.1.property ij.2.property hP
  have hex (ij : I × I) :=
    _root_.Algebra.FiniteType.exists_ne_zero_algebraMap_eq_zero_of_isEmpty_algHom R K
      (Algebra P (fun e : BoundedMonomial σ P.totalDegree => e.val) ij.1.val ij.2.val)
      Ω (hempty ij)
  choose a ha hkill using hex
  obtain ⟨e, he, hcoeff⟩ := exists_nonconstant_coeff
    (map (algebraMap R Ω) P) hP.ne_zero hP.not_isUnit
  have hPe : P.coeff e ≠ 0 := by
    intro h
    exact hcoeff (by simp only [coeff_map, h, map_zero])
  let r : R := P.coeff e * ∏ ij : I × I, a ij
  refine ⟨r, mul_ne_zero hPe (Finset.prod_ne_zero_iff.mpr (fun ij _ => ha ij)), ?_⟩
  intro L _ φ hr
  let : _root_.Algebra R L := φ.toAlgebra
  have hprod : φ (P.coeff e) ≠ 0 ∧ ∀ ij : I × I, φ (a ij) ≠ 0 := by
    simpa only [r, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
      Finset.mem_univ, forall_const] using hr
  have hmapcoeff : (map φ P).coeff e ≠ 0 := by
    simpa only [coeff_map] using hprod.1
  have hmapne : map φ P ≠ 0 := by
    intro h
    exact hmapcoeff (by simp only [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply])
  refine ⟨not_isUnit_of_nonconstant_coeff he hmapcoeff, ?_⟩
  intro Q T hfac
  by_contra hunit
  push Not at hunit
  have hQ : Q ≠ 0 := by intro h; exact hmapne (by simpa only [h, zero_mul] using hfac)
  have hT : T ≠ 0 := by intro h; exact hmapne (by simpa only [h, mul_zero] using hfac)
  have hdeg : (map φ P).totalDegree ≤ P.totalDegree :=
    Finset.sup_mono (support_map_subset φ P)
  have hQdeg : Q.totalDegree ≤ P.totalDegree :=
    (totalDegree_le_of_dvd_of_isDomain ⟨T, hfac⟩ hmapne).trans hdeg
  have hTdeg : T.totalDegree ≤ P.totalDegree :=
    (totalDegree_le_of_dvd_of_isDomain ⟨Q, hfac.trans (mul_comm Q T)⟩
      hmapne).trans hdeg
  obtain ⟨ei, hei, hQi⟩ := exists_nonconstant_coeff Q hQ hunit.1
  obtain ⟨ej, hej, hTj⟩ := exists_nonconstant_coeff T hT hunit.2
  let i : I := ⟨⟨ei, fun s => (monomial_le_degreeOf s (mem_support_iff.mpr hQi)).trans
    ((degreeOf_le_totalDegree Q s).trans hQdeg)⟩, hei⟩
  let j : I := ⟨⟨ej, fun s => (monomial_le_degreeOf s (mem_support_iff.mpr hTj)).trans
    ((degreeOf_le_totalDegree T s).trans hTdeg)⟩, hej⟩
  obtain ⟨f⟩ := (nonempty_algHom_iff (S := L) P
    (fun z : BoundedMonomial σ P.totalDegree => z.val) i.val j.val).mpr
    ⟨fun z => Q.coeff z.val, fun z => T.coeff z.val,
      (Q.coeff ei)⁻¹, (T.coeff ej)⁻¹, by
        rw [polynomial_bounded_coeff Q _ hQdeg, polynomial_bounded_coeff T _ hTdeg]
        exact hfac,
      inv_mul_cancel₀ hQi, inv_mul_cancel₀ hTj⟩
  apply hprod.2 (i, j)
  change algebraMap R L (a (i, j)) = 0
  rw [← f.commutes, hkill (i, j), map_zero]

end MvPolynomial.FactorizationAlgebra
