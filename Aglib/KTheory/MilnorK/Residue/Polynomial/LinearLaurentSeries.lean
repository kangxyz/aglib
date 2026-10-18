/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Polynomial.LaurentSeries
public import Aglib.KTheory.MilnorK.Residue.Polynomial.LinearPlace

/-!
# The actual Laurent-series residue at a linear polynomial place

Polynomial translation `X ↦ X + a` identifies the uniformizer `X - a` with the
power-series variable. The localization and fraction-field maps are constructed
from that literal substitution, and their actual residue-field map is evaluation
at `a`. Thus the original all-degree residue at every linear place agrees with
the power-series DVR residue. Combined with residue-field extension, this gives
a concrete complete-DVR realization of each original finite polynomial residue.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace Polynomial.LocalResidue

variable {k : Type*} [Field k] (a : k)

local instance : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩

/-- Literal polynomial substitution `q(X) ↦ q(X + a)` followed by the inclusion
into power series. Translation is the native polynomial algebra equivalence. -/
def linearPlacePolynomialMap : k[X] →+* PowerSeries k :=
  Polynomial.coeToPowerSeries.ringHom.comp (algEquivAevalXAddC a).toRingHom

/-- Translation loses no polynomial information. -/
theorem linearPlacePolynomialMap_injective : Function.Injective (linearPlacePolynomialMap a) :=
  (Polynomial.coe_injective k).comp (algEquivAevalXAddC a).injective

/-- At the translated origin, constant coefficient is evaluation at the original point. -/
@[simp]
theorem linearPlacePolynomialMap_constantCoeff (q : k[X]) :
    PowerSeries.constantCoeff (linearPlacePolynomialMap a q) = q.eval a := by
  change PowerSeries.constantCoeff ((algEquivAevalXAddC a q : k[X]) : PowerSeries k) = _
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
  simp [algEquivAevalXAddC_apply, ← comp_eq_aeval]

/-- The original linear uniformizer maps literally to the power-series variable. -/
@[simp]
theorem linearPlacePolynomialMap_uniformizer :
    linearPlacePolynomialMap a (X - C a) = PowerSeries.X := by
  simp [linearPlacePolynomialMap, algEquivAevalXAddC_apply]

/-- Every denominator allowed in the original localization is a power-series unit. -/
theorem linearPlacePolynomialMap_isUnit (q : (primeIdeal (X - C a)).primeCompl) :
    IsUnit (linearPlacePolynomialMap a (q : k[X])) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, linearPlacePolynomialMap_constantCoeff,
    isUnit_iff_ne_zero]
  intro h
  exact q.property (Ideal.mem_span_singleton.mpr (dvd_iff_isRoot.mpr h))

/-- The actual map from the local ring at `X - a` into the power-series DVR. -/
def linearPlacePowerSeriesMap : Ring (X - C a) →+* PowerSeries k :=
  IsLocalization.lift (S := Ring (X - C a)) (linearPlacePolynomialMap_isUnit a)

@[simp]
theorem linearPlacePowerSeriesMap_polynomial (q : k[X]) :
    linearPlacePowerSeriesMap a (algebraMap k[X] (Ring (X - C a)) q) =
      linearPlacePolynomialMap a q :=
  IsLocalization.lift_eq (linearPlacePolynomialMap_isUnit a) q

theorem linearPlacePowerSeriesMap_uniformizer :
    linearPlacePowerSeriesMap a (algebraMap k[X] (Ring (X - C a)) (X - C a)) =
      PowerSeries.X := by
  rw [linearPlacePowerSeriesMap_polynomial, linearPlacePolynomialMap_uniformizer]

instance linearPlacePowerSeriesMap_isLocalHom : IsLocalHom (linearPlacePowerSeriesMap a) := by
  apply ((IsLocalRing.local_hom_TFAE (linearPlacePowerSeriesMap a)).out 4 1).mp
  rw [maximalIdeal_eq_span, Ideal.span_singleton_le_iff_mem]
  change linearPlacePowerSeriesMap a (algebraMap k[X] (Ring (X - C a)) (X - C a)) ∈
    IsLocalRing.maximalIdeal (PowerSeries k)
  rw [linearPlacePowerSeriesMap_uniformizer]
  exact PowerSeries.X_irreducible.not_isUnit

/-- The literal translated polynomial map into Laurent series is injective. -/
theorem linearPlaceLaurentPolynomialMap_injective :
    Function.Injective ((algebraMap (PowerSeries k) (LaurentSeries k)).comp
      (linearPlacePolynomialMap a)) :=
  (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).comp
    (linearPlacePolynomialMap_injective a)

/-- The native rational-function lift of the literal translated polynomial map. -/
def linearPlaceLaurentSeriesMap : RatFunc k →+* LaurentSeries k :=
  RatFunc.liftRingHom ((algebraMap (PowerSeries k) (LaurentSeries k)).comp
    (linearPlacePolynomialMap a)) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (linearPlaceLaurentPolynomialMap_injective a))

@[simp]
theorem linearPlaceLaurentSeriesMap_polynomial (q : k[X]) :
    linearPlaceLaurentSeriesMap a (algebraMap k[X] (RatFunc k) q) =
      algebraMap (PowerSeries k) (LaurentSeries k) (linearPlacePolynomialMap a q) :=
  RatFunc.liftRingHom_algebraMap _ _ q

/-- The translated rational-function inclusion and local-ring inclusion commute
inside the native Laurent-series fraction field. -/
theorem linearPlacePowerSeriesMap_fraction (r : Ring (X - C a)) :
    linearPlaceLaurentSeriesMap a (algebraMap (Ring (X - C a)) (RatFunc k) r) =
      algebraMap (PowerSeries k) (LaurentSeries k) (linearPlacePowerSeriesMap a r) := by
  have h : (linearPlaceLaurentSeriesMap a).comp
        (algebraMap (Ring (X - C a)) (RatFunc k)) =
      (algebraMap (PowerSeries k) (LaurentSeries k)).comp (linearPlacePowerSeriesMap a) := by
    apply IsLocalization.ringHom_ext (primeIdeal (X - C a)).primeCompl
    apply RingHom.ext
    intro q
    simp only [RingHom.comp_apply, linearPlacePowerSeriesMap_polynomial,
      ← IsScalarTower.algebraMap_apply k[X] (Ring (X - C a)) (RatFunc k),
      linearPlaceLaurentSeriesMap_polynomial]
  exact RingHom.congr_fun h r

/-- The actual residue-field map is the original evaluation identification. -/
theorem linearPlacePowerSeriesMap_residue (b : ResidueField (X - C a)) :
    PowerSeries.residueFieldOfPowerSeries
        (IsLocalRing.ResidueField.map (linearPlacePowerSeriesMap a) b) =
      MilnorK.PolynomialResidue.linearRootEquiv a
        (residueEquiv (X - C a) b) := by
  obtain ⟨b, rfl⟩ := (adjoinRootEquiv (X - C a)).surjective b
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
  rw [adjoinRootEquiv_mk]
  change PowerSeries.residueFieldOfPowerSeries
    (IsLocalRing.ResidueField.map (linearPlacePowerSeriesMap a)
      (IsLocalRing.residue (Ring (X - C a))
        (algebraMap k[X] (Ring (X - C a)) q))) = _
  rw [IsLocalRing.ResidueField.map_residue, linearPlacePowerSeriesMap_polynomial,
    powerSeries_residueEquiv_residue, residueEquiv_algebraMap,
    MilnorK.PolynomialResidue.linearRootEquiv_mk,
    linearPlacePolynomialMap_constantCoeff]

end Polynomial.LocalResidue

namespace MilnorK.PolynomialResidue

open Polynomial Polynomial.LocalResidue

variable {k : Type*} [Field k]

local instance (a : k) : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩

/-- The original residue at `X - a` equals the complete-DVR residue after literal
translation into Laurent series, in every Milnor degree and characteristic. -/
theorem residueAt_linear_eq_laurentSeries_residue (a : k)
    (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    MilnorK.map n (linearRootEquiv a).toRingHom (residueAt (X - C a) n x) =
      MilnorK.map n PowerSeries.residueFieldOfPowerSeries.toRingHom
        (DVR.residue (PowerSeries k) (LaurentSeries k) n
          (MilnorK.map (n + 1) (linearPlaceLaurentSeriesMap a) x)) := by
  have hirr : Irreducible (linearPlacePowerSeriesMap a
      (algebraMap k[X] (Ring (X - C a)) (X - C a))) := by
    rw [linearPlacePowerSeriesMap_uniformizer]
    exact PowerSeries.X_irreducible
  have hdvr := DVR.residue_restrict_apply (linearPlacePowerSeriesMap a)
    (linearPlaceLaurentSeriesMap a) (linearPlacePowerSeriesMap_fraction a)
    (irreducible_polynomial (X - C a)) hirr n x
  have hsquare : PowerSeries.residueFieldOfPowerSeries.toRingHom.comp
      (IsLocalRing.ResidueField.map (linearPlacePowerSeriesMap a)) =
        (linearRootEquiv a).toRingHom.comp (residueEquiv (X - C a)).toRingHom := by
    apply RingHom.ext
    exact linearPlacePowerSeriesMap_residue a
  rw [residueAt_eq_dvr, LinearMap.comp_apply, ← hdvr]
  change ((MilnorK.map n (linearRootEquiv a).toRingHom).comp
    (MilnorK.map n (residueEquiv (X - C a)).toRingHom)) _ =
      ((MilnorK.map n PowerSeries.residueFieldOfPowerSeries.toRingHom).comp
        (MilnorK.map n (IsLocalRing.ResidueField.map (linearPlacePowerSeriesMap a)))) _
  rw [← MilnorK.map_comp, ← MilnorK.map_comp, hsquare]

/-- Every original finite polynomial residue in characteristic zero is recovered
exactly in the native complete DVR over its actual root residue field. -/
theorem residueAt_eq_root_laurentSeries_residue [CharZero k]
    (p : k[X]) [Fact (Irreducible p)] (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    residueAt p n x =
      MilnorK.map n PowerSeries.residueFieldOfPowerSeries.toRingHom
        (DVR.residue (PowerSeries (AdjoinRoot p)) (LaurentSeries (AdjoinRoot p)) n
          (MilnorK.map (n + 1)
            ((linearPlaceLaurentSeriesMap (AdjoinRoot.root p)).comp
              (fractionMap (algebraMap k (AdjoinRoot p)))) x)) := by
  rw [MilnorK.map_comp, LinearMap.comp_apply, ← residueAt_linear_eq_laurentSeries_residue]
  exact residueAt_eq_linearPlace p n x

end MilnorK.PolynomialResidue
