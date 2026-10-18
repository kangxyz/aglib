/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalFunction

/-!
# Full coefficient base change for the actual rational-function norm

Constant extension of a rational-function presentation has exactly the original
constant-field branches. Reindexing the proved polynomial norm base-change
formula gives the full branch sum on the actual rational-function fields.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue
open scoped RatFunc

attribute [local instance] Polynomial.algebra

variable {k H : Type*} [Field k] [Field H]

/-- Coefficient extension of a constant presentation is the constant
presentation of its coefficient extension. -/
theorem rationalCoefficient_map_fractionMap (φ : k →+* H) (p : k[X]) :
    (p.map RatFunc.C).map (fractionMap φ) = (p.map φ).map RatFunc.C := by
  simp only [Polynomial.map_map]
  congr 1
  ext a
  exact fractionMap_C φ a

/-- No new irreducible branch appears on passing from a field to its
rational-function field. -/
theorem exists_rationalCoefficient_factor (a : H[X]) (ha : a.Monic)
    (r : MonicIrreducible (RatFunc H)) (hr : r.val ∣ a.map RatFunc.C) :
    ∃ q : MonicIrreducible H, q.val ∣ a ∧ rationalCoefficientPolynomial q = r := by
  classical
  have hprod : (UniqueFactorizationMonoid.normalizedFactors a).prod = a := by
    simpa only [ha.leadingCoeff, Polynomial.C_1, one_mul] using
      Polynomial.leadingCoeff_mul_prod_normalizedFactors a
  have hd : r.val ∣ ((UniqueFactorizationMonoid.normalizedFactors a).map
      (Polynomial.mapRingHom (RatFunc.C : H →+* RatFunc H))).prod := by
    rw [← map_multiset_prod, hprod]
    exact hr
  obtain ⟨b, hb, hdiv⟩ := r.property.2.prime.exists_mem_multiset_dvd hd
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hb
  obtain ⟨hqi, hqm, hqd⟩ := (Polynomial.mem_normalizedFactors_iff ha.ne_zero).mp hq
  refine ⟨⟨q, hqm, hqi⟩, hqd, ?_⟩
  apply Subtype.ext
  exact Polynomial.eq_of_monic_of_associated (hqm.map _) r.property.1
    (r.property.2.associated_of_dvd (hqm.irreducible_map_ratFunc_C hqi) hdiv).symm

/-- The actual coefficient-image factor family is unchanged by adjoining the
rational variable. -/
def rationalCoefficientPlacesEquiv (φ : k →+* H) (p : MonicIrreducible k) :
    {q // q ∈ placesAbove φ p} ≃
      {r // r ∈ placesAbove (fractionMap φ) (rationalCoefficientPolynomial p)} := by
  classical
  refine Equiv.ofBijective (fun q => ⟨rationalCoefficientPolynomial q.val, ?_⟩) ?_
  · rw [mem_placesAbove]
    change q.val.val.map RatFunc.C ∣ (p.val.map RatFunc.C).map (fractionMap φ)
    rw [rationalCoefficient_map_fractionMap]
    exact Polynomial.map_dvd _ ((mem_placesAbove φ p q.val).mp q.property)
  · constructor
    · intro q r h
      apply Subtype.ext
      apply Subtype.ext
      have hm := congrArg (fun q => q.val.val) h
      exact Polynomial.map_injective RatFunc.C RatFunc.C_injective hm
    · intro r
      have hd := (mem_placesAbove (fractionMap φ) (rationalCoefficientPolynomial p)
        r.val).mp r.property
      change r.val.val ∣ (p.val.map RatFunc.C).map (fractionMap φ) at hd
      rw [rationalCoefficient_map_fractionMap] at hd
      obtain ⟨q, hq, he⟩ := exists_rationalCoefficient_factor (p.val.map φ)
        (p.property.1.map φ) r.val hd
      exact ⟨⟨q, (mem_placesAbove φ p q).mpr hq⟩, Subtype.ext he⟩

@[simp]
theorem rationalCoefficientPlacesEquiv_apply (φ : k →+* H) (p : MonicIrreducible k)
    (q : {q // q ∈ placesAbove φ p}) :
    (rationalCoefficientPlacesEquiv φ p q).val = rationalCoefficientPolynomial q.val := rfl

local instance (p : MonicIrreducible k) :
    Fact (Irreducible (p.val.map (RatFunc.C : k →+* RatFunc k))) :=
  ⟨p.property.1.irreducible_map_ratFunc_C p.property.2⟩

/-- Literal rational coefficient maps commute with the literal quotient map
of each constant-field branch. -/
theorem rationalCoefficientAlgEquiv_comp_adjoinRootMap (φ : k →+* H)
    (p : MonicIrreducible k) (q : MonicIrreducible H) (hq : q.val ∣ p.val.map φ) :
    (AdjoinRoot.rationalCoefficientAlgEquiv q.val q.property.1).toRingHom.comp
      (adjoinRootMap (fractionMap φ) (p.val.map RatFunc.C) (q.val.map RatFunc.C)
        (by rw [rationalCoefficient_map_fractionMap]; exact Polynomial.map_dvd _ hq)) =
      (fractionMap (adjoinRootMap φ p.val q.val hq)).comp
        (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).toRingHom := by
  have hc : (fractionMap (algebraMap H (AdjoinRoot q.val))).comp (fractionMap φ) =
      (fractionMap (adjoinRootMap φ p.val q.val hq)).comp
        (fractionMap (algebraMap k (AdjoinRoot p.val))) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RatFunc.algebraMap_C, fractionMap_C,
        adjoinRootMap_algebraMap]
    · simp only [RingHom.comp_apply, RatFunc.algebraMap_X, fractionMap_X]
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change (AdjoinRoot.rationalCoefficientAlgEquiv q.val q.property.1)
      (adjoinRootMap (fractionMap φ) (p.val.map RatFunc.C) (q.val.map RatFunc.C) _
        (algebraMap (RatFunc k) (AdjoinRoot (p.val.map RatFunc.C)) a)) =
      fractionMap (adjoinRootMap φ p.val q.val hq)
        ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
          (algebraMap (RatFunc k) (AdjoinRoot (p.val.map RatFunc.C)) a))
    rw [adjoinRootMap_algebraMap, AdjoinRoot.rationalCoefficientAlgEquiv_algebraMap,
      AdjoinRoot.rationalCoefficientAlgEquiv_algebraMap]
    exact RingHom.congr_fun hc a
  · change (AdjoinRoot.rationalCoefficientAlgEquiv q.val q.property.1)
      (adjoinRootMap (fractionMap φ) (p.val.map RatFunc.C) (q.val.map RatFunc.C) _
        (AdjoinRoot.root (p.val.map RatFunc.C))) =
      fractionMap (adjoinRootMap φ p.val q.val hq)
        ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
          (AdjoinRoot.root (p.val.map RatFunc.C)))
    rw [adjoinRootMap_root, AdjoinRoot.rationalCoefficientAlgEquiv_root,
      AdjoinRoot.rationalCoefficientAlgEquiv_root, fractionMap_C, adjoinRootMap_root]

/-- The inverse identifications retain the same actual branch field maps. -/
theorem rationalCoefficientAlgEquiv_symm_comp_fractionMap (φ : k →+* H)
    (p : MonicIrreducible k) (q : MonicIrreducible H) (hq : q.val ∣ p.val.map φ) :
    (AdjoinRoot.rationalCoefficientAlgEquiv q.val q.property.1).symm.toRingHom.comp
      (fractionMap (adjoinRootMap φ p.val q.val hq)) =
      (adjoinRootMap (fractionMap φ) (p.val.map RatFunc.C) (q.val.map RatFunc.C)
        (by rw [rationalCoefficient_map_fractionMap]; exact Polynomial.map_dvd _ hq)).comp
          (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom := by
  apply RingHom.ext
  intro x
  apply (AdjoinRoot.rationalCoefficientAlgEquiv q.val q.property.1).injective
  have h := RingHom.congr_fun
    (rationalCoefficientAlgEquiv_comp_adjoinRootMap φ p q hq)
      ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm x)
  change (AdjoinRoot.rationalCoefficientAlgEquiv q.val q.property.1)
    ((AdjoinRoot.rationalCoefficientAlgEquiv q.val q.property.1).symm
      (fractionMap (adjoinRootMap φ p.val q.val hq) x)) = _
  rw [AlgEquiv.apply_symm_apply]
  change (AdjoinRoot.rationalCoefficientAlgEquiv q.val q.property.1)
    (adjoinRootMap (fractionMap φ) (p.val.map RatFunc.C) (q.val.map RatFunc.C) _
      ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm x)) =
    fractionMap (adjoinRootMap φ p.val q.val hq)
      ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
        ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm x)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

open scoped Classical in
/-- Coefficient restriction of the actual rational-function norm is the full
sum of actual rational-function norms of all constant-field branches. -/
theorem rationalFunctionNorm_restrict [CharZero k]
    (φ : k →+* H) (n : ℕ) (p : MonicIrreducible k)
    (x : K (RatFunc (AdjoinRoot p.val)) n) :
    MilnorK.map n (fractionMap φ) (rationalFunctionNorm n p x) =
      ∑ q ∈ (placesAbove φ p).attach,
        rationalFunctionNorm n q.val
          (MilnorK.map n (fractionMap (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property))) x) := by
  classical
  unfold rationalFunctionNorm
  simp only [LinearMap.comp_apply]
  rw [polynomialNorm_restrict]
  simp only [Finset.attach_eq_univ]
  symm
  apply Fintype.sum_equiv (rationalCoefficientPlacesEquiv φ p)
  intro q
  change polynomialNorm n (rationalCoefficientPolynomial q.val)
    (MilnorK.map n
      (AdjoinRoot.rationalCoefficientAlgEquiv q.val.val q.val.property.1).symm.toRingHom
      (MilnorK.map n (fractionMap (adjoinRootMap φ p.val q.val.val _)) x)) =
    polynomialNorm n (rationalCoefficientPolynomial q.val)
      (MilnorK.map n (adjoinRootMap (fractionMap φ) (p.val.map RatFunc.C)
        (q.val.val.map RatFunc.C) _)
        (MilnorK.map n
          (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom x))
  apply congrArg (polynomialNorm n (rationalCoefficientPolynomial q.val))
  have h := congrArg (MilnorK.map n)
    (rationalCoefficientAlgEquiv_symm_comp_fractionMap φ p q.val
      ((mem_placesAbove φ p q.val).mp q.property))
  rw [map_comp, map_comp] at h
  exact LinearMap.congr_fun h x

open scoped Classical in
/-- The full rational coefficient base-change formula as an equality of
integer-linear maps, including degree zero. -/
theorem rationalFunctionNorm_comp_restrict [CharZero k]
    (φ : k →+* H) (n : ℕ) (p : MonicIrreducible k) :
    (MilnorK.map n (fractionMap φ)).comp (rationalFunctionNorm n p) =
      ∑ q ∈ (placesAbove φ p).attach,
        (rationalFunctionNorm n q.val).comp
          (MilnorK.map n (fractionMap (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)))) := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using
    rationalFunctionNorm_restrict φ n p x

end MilnorK.PolynomialNorm
