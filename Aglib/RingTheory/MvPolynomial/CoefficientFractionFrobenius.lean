/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.CrossFieldFrobenius
public import Aglib.RingTheory.Localization.FrobeniusLinearIndependent
public import Aglib.FieldTheory.SeparablyGenerated.FrobeniusCriterion
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Geometric reducedness under rational coefficient extension

Polynomial independence is embedded into the existing power-series coefficient
argument and reflected back. Native localization clears the vector denominators.
All field actions below retain their supplied compatible polynomial maps.
-/

@[expose] public noncomputable section

namespace MvPolynomial

attribute [local instance] algebraMvPolynomial

/-- The ordinary polynomial-to-series injection respects polynomial scalars
from a smaller coefficient field. -/
def coeToMvPowerSeries.coefficientAlgHom
    (k K σ : Type*) [Field k] [Field K] [Algebra k K] :
    MvPolynomial σ K →ₐ[MvPolynomial σ k] MvPowerSeries σ K :=
  { coeToMvPowerSeries.ringHom with
    commutes' := fun q => by
      change ((map (algebraMap k K) q : MvPolynomial σ K) : MvPowerSeries σ K) =
        MvPowerSeries.map (algebraMap k K) (q : MvPowerSeries σ k)
      ext d
      simp only [coeff_coe, coeff_map, MvPowerSeries.coeff_map] }

/-- The cross-field series argument restricts to polynomials, with the actual
coefficient-extension algebra structure. -/
lemma linearIndependent_pow_over_mvPolynomial_of_geometricallyReduced
    {k K σ ι : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra.IsGeometricallyReduced k K] [Finite ι]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (f : ι → MvPolynomial σ K)
    (hf : LinearIndependent (MvPolynomial σ k) f) :
    LinearIndependent (MvPolynomial σ k) (fun i => f i ^ p) := by
  let m := coeToMvPowerSeries.coefficientAlgHom k K σ
  have hm : Function.Injective m := coe_injective σ K
  have hfm := hf.map' m.toLinearMap (LinearMap.ker_eq_bot.mpr hm)
  have hpowers := MvPowerSeries.linearIndependent_pow_over_mvPolynomial_of_geometricallyReduced
    p hp (fun i => m (f i)) hfm
  apply LinearIndependent.of_comp m.toLinearMap
  change LinearIndependent (MvPolynomial σ k) (fun i => m (f i ^ p))
  simpa only [map_pow] using hpowers

/-- Geometrically reduced coefficient extensions preserve finite rational
Frobenius independence. Neither coefficient field has finite p-rank imposed. -/
lemma linearIndependent_pow_over_fractionRing_of_geometricallyReduced_coefficients
    {k K F G σ ι : Type*} [Field k] [Field K] [Field F] [Field G]
    [Algebra k K] [Algebra.IsGeometricallyReduced k K]
    [Algebra (MvPolynomial σ k) F] [IsFractionRing (MvPolynomial σ k) F]
    [Algebra (MvPolynomial σ K) G] [IsFractionRing (MvPolynomial σ K) G]
    [Algebra (MvPolynomial σ k) G]
    [IsScalarTower (MvPolynomial σ k) (MvPolynomial σ K) G]
    [Algebra F G] [IsScalarTower (MvPolynomial σ k) F G] [Finite ι]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (f : ι → G) (hf : LinearIndependent F f) :
    LinearIndependent F (fun i => f i ^ p) := by
  exact IsFractionRing.linearIndependent_pow_of_domain
    (R := MvPolynomial σ k) (S := MvPolynomial σ K) (F := F) (L := G) p
    (fun g hg => linearIndependent_pow_over_mvPolynomial_of_geometricallyReduced p hp g hg)
    f hf

/-- The actual rational coefficient extension is geometrically reduced in
positive characteristic. Characteristic zero is handled by the existing field endpoint. -/
lemma isGeometricallyReduced_fractionRing_of_geometricallyReduced_coefficients
    {k K F G σ : Type*} [Field k] [Field K] [Field F] [Field G]
    [Algebra k K] [Algebra.IsGeometricallyReduced k K]
    [Algebra (MvPolynomial σ k) F] [IsFractionRing (MvPolynomial σ k) F]
    [Algebra (MvPolynomial σ K) G] [IsFractionRing (MvPolynomial σ K) G]
    [Algebra (MvPolynomial σ k) G]
    [IsScalarTower (MvPolynomial σ k) (MvPolynomial σ K) G]
    [Algebra F G] [IsScalarTower (MvPolynomial σ k) F G]
    (p : ℕ) (hp : p.Prime) [ExpChar k p] [ExpChar F p] :
    Algebra.IsGeometricallyReduced F G := by
  apply Algebra.isGeometricallyReduced_of_linearIndependent_pow p hp
  intro n f hf
  exact linearIndependent_pow_over_fractionRing_of_geometricallyReduced_coefficients
    (k := k) (K := K) (σ := σ) p hp f hf

end MvPolynomial
