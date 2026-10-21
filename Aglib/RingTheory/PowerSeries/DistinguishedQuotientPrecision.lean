/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.MvPolynomial.FormalDivisibilityEquations
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Precision of the actual distinguished polynomial quotient

A polynomial point close to an exact formal solution modulo a distinguished
polynomial squared times an ideal has its actual polynomial quotient in that
ideal. Quotient smallness is proved by evaluation in a quotient ring and
uniqueness of Weierstrass division. The ideal is an ideal of the full power-series
ring, so this applies to mixed maximal-adic precision without asserting that
all coefficients separately have the same coefficient-adic precision.
-/

@[expose] public section

namespace PowerSeries

variable {A B σ : Type*} [CommRing A] [CommRing B] [IsLocalRing B]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- The actual monic-division quotient inherits the formal error ideal. -/
theorem divByMonic_sq_mem_of_eval_eq_zero (P : Polynomial B)
    (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal B))
    (φ : A →+* B) (F : MvPolynomial σ (Polynomial A))
    (y : σ → PowerSeries B) (r : σ → Polynomial B) (a : Ideal (PowerSeries B))
    (hy : MvPolynomial.eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ)) y F = 0)
    (hr : ∀ i, (r i : PowerSeries B) - y i ∈
      Ideal.span {((P ^ 2 : Polynomial B) : PowerSeries B)} * a) :
    ((MvPolynomial.eval₂Hom (Polynomial.mapRingHom φ) r F /ₘ P ^ 2 : Polynomial B) :
      PowerSeries B) ∈ a := by
  let E := MvPolynomial.eval₂Hom (Polynomial.mapRingHom φ) r F
  let K : Ideal (PowerSeries B) := Ideal.span {((P ^ 2 : Polynomial B) : PowerSeries B)} * a
  let π := Ideal.Quotient.mk K
  have hpoint : (fun i ↦ π (r i : PowerSeries B)) = (fun i ↦ π (y i)) := by
    funext i
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hr i)
  have hcoe : (E : PowerSeries B) = MvPolynomial.eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ))
      (fun i ↦ (r i : PowerSeries B)) F := by
    simpa only [E, Polynomial.coeToPowerSeries.ringHom_apply] using
      MvPolynomial.map_eval₂Hom (Polynomial.mapRingHom φ) r
        Polynomial.coeToPowerSeries.ringHom F
  have hzero : π (E : PowerSeries B) = 0 := by
    rw [hcoe, MvPolynomial.map_eval₂Hom, hpoint, ← MvPolynomial.map_eval₂Hom, hy,
      map_zero]
  have hmem : (E : PowerSeries B) ∈ K := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  obtain ⟨q, hq, heq⟩ := Ideal.mem_span_singleton_mul.mp hmem
  have hP2 : (P ^ 2).IsDistinguishedAt (IsLocalRing.maximalIdeal B) := by
    simpa only [pow_two] using hP.mul hP
  have hdvd : P ^ 2 ∣ E := (hP2.coe_dvd_coe_iff E).mp ⟨q, heq.symm⟩
  have hrem : E %ₘ P ^ 2 = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hP2.monic).mpr hdvd
  have hpoly : P ^ 2 * (E /ₘ P ^ 2) = E := by
    have h := Polynomial.modByMonic_add_div E (P ^ 2)
    rw [hrem, zero_add] at h
    exact h
  have hmul : ((P ^ 2 : Polynomial B) : PowerSeries B) *
      ((E /ₘ P ^ 2 : Polynomial B) : PowerSeries B) =
      ((P ^ 2 : Polynomial B) : PowerSeries B) * q := by
    rw [← Polynomial.coe_mul, hpoly, heq]
  have hquot : ((E /ₘ P ^ 2 : Polynomial B) : PowerSeries B) = q :=
    (hP2.isWeierstrassDivisorAt'.eq_of_mul_add_eq_mul_add
      (r := 0) (r' := 0) (by simp) (by simp) (by simpa using hmul)).1
  change ((E /ₘ P ^ 2 : Polynomial B) : PowerSeries B) ∈ a
  rw [hquot]
  exact hq

end PowerSeries
