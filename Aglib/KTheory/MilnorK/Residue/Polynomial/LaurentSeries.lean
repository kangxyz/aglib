/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Restriction
public import Aglib.KTheory.MilnorK.InfinityResidue
public import Mathlib.RingTheory.LaurentSeries

/-!
# The actual residue square at the Laurent-series completion

The polynomial local ring at `X` maps to the power-series DVR by the literal
polynomial inclusion. Its fraction-field map is the native algebra map from
rational functions to Laurent series. The uniformizer remains `X`, and the
residue map is the identity on the coefficient field. Consequently the original
polynomial residue agrees in every Milnor degree with the power-series DVR
residue after actual Laurent-series restriction.
-/

@[expose] public noncomputable section

open scoped RatFunc

namespace Polynomial.LocalResidue

variable (k : Type*) [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

theorem coeToPowerSeries_isUnit (q : (primeIdeal (X : k[X])).primeCompl) :
    IsUnit (Polynomial.coeToPowerSeries.ringHom (q : k[X]) : PowerSeries k) := by
  rw [Polynomial.coeToPowerSeries.ringHom_apply, PowerSeries.isUnit_iff_constantCoeff,
    Polynomial.constantCoeff_coe, isUnit_iff_ne_zero]
  intro h
  exact q.property (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr h))

/-- The actual inclusion of the polynomial local DVR at `X` into power series. -/
def xPlacePowerSeriesMap : Ring (X : k[X]) →+* PowerSeries k :=
  IsLocalization.lift (S := Ring (X : k[X])) (coeToPowerSeries_isUnit k)

@[simp]
theorem xPlacePowerSeriesMap_polynomial (q : k[X]) :
    xPlacePowerSeriesMap k (algebraMap k[X] (Ring (X : k[X])) q) =
      (q : PowerSeries k) :=
  IsLocalization.lift_eq (coeToPowerSeries_isUnit k) q

/-- The source uniformizer goes literally to the target uniformizer. -/
theorem xPlacePowerSeriesMap_X :
    xPlacePowerSeriesMap k (algebraMap k[X] (Ring (X : k[X])) X) = PowerSeries.X := by
  rw [xPlacePowerSeriesMap_polynomial, Polynomial.coe_X]

instance xPlacePowerSeriesMap_isLocalHom : IsLocalHom (xPlacePowerSeriesMap k) := by
  apply ((IsLocalRing.local_hom_TFAE (xPlacePowerSeriesMap k)).out 4 1).mp
  rw [maximalIdeal_eq_span, Ideal.span_singleton_le_iff_mem]
  change xPlacePowerSeriesMap k (algebraMap k[X] (Ring (X : k[X])) X) ∈
    IsLocalRing.maximalIdeal (PowerSeries k)
  rw [xPlacePowerSeriesMap_X]
  exact PowerSeries.X_irreducible.not_isUnit

/-- The native rational-function inclusion and the actual local ring inclusion
commute inside the native Laurent-series fraction field. -/
theorem xPlacePowerSeriesMap_fraction (r : Ring (X : k[X])) :
    algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap (Ring (X : k[X])) (RatFunc k) r) =
      algebraMap (PowerSeries k) (LaurentSeries k) (xPlacePowerSeriesMap k r) := by
  have h : (algebraMap (RatFunc k) (LaurentSeries k)).comp
        (algebraMap (Ring (X : k[X])) (RatFunc k)) =
      (algebraMap (PowerSeries k) (LaurentSeries k)).comp (xPlacePowerSeriesMap k) := by
    apply IsLocalization.ringHom_ext (primeIdeal (X : k[X])).primeCompl
    apply RingHom.ext
    intro q
    simp only [RingHom.comp_apply, xPlacePowerSeriesMap_polynomial,
      ← IsScalarTower.algebraMap_apply k[X] (Ring (X : k[X])) (RatFunc k)]
    exact (RatFunc.coe_coe q).symm
  exact RingHom.congr_fun h r

/-- The native power-series residue-field equivalence is literal constant
coefficient reduction. -/
@[simp]
theorem powerSeries_residueEquiv_residue (r : PowerSeries k) :
    PowerSeries.residueFieldOfPowerSeries (IsLocalRing.residue (PowerSeries k) r) =
      PowerSeries.constantCoeff r := rfl

/-- Under the original quotient identifications, the actual residue-field map
at `X` is the identity on the coefficient field. -/
theorem xPlacePowerSeriesMap_residue (a : ResidueField (X : k[X])) :
    PowerSeries.residueFieldOfPowerSeries
        (IsLocalRing.ResidueField.map (xPlacePowerSeriesMap k) a) =
      MilnorK.InfinityResidue.rootXEquiv k
        (residueEquiv (X : k[X]) a) := by
  obtain ⟨b, rfl⟩ := (adjoinRootEquiv (X : k[X])).surjective a
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
  rw [adjoinRootEquiv_mk]
  change PowerSeries.residueFieldOfPowerSeries
    (IsLocalRing.ResidueField.map (xPlacePowerSeriesMap k)
      (IsLocalRing.residue (Ring (X : k[X]))
        (algebraMap k[X] (Ring (X : k[X])) q))) = _
  rw [IsLocalRing.ResidueField.map_residue, xPlacePowerSeriesMap_polynomial,
    powerSeries_residueEquiv_residue, residueEquiv_algebraMap,
    MilnorK.InfinityResidue.rootXEquiv_mk, Polynomial.constantCoeff_coe]
  exact Polynomial.coeff_zero_eq_eval_zero q

end Polynomial.LocalResidue

namespace MilnorK.PolynomialResidue

open Polynomial Polynomial.LocalResidue

variable (k : Type*) [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- The original residue at `X`, identified with the coefficient field, equals
the actual power-series DVR residue of the Laurent-series image in every degree. -/
theorem residueAt_X_eq_laurentSeries_residue (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    MilnorK.map n (InfinityResidue.rootXEquiv k).toRingHom
        (residueAt (X : k[X]) n x) =
      MilnorK.map n PowerSeries.residueFieldOfPowerSeries.toRingHom
        (DVR.residue (PowerSeries k) (LaurentSeries k) n
          (MilnorK.map (n + 1) (algebraMap (RatFunc k) (LaurentSeries k)) x)) := by
  have hirr : Irreducible (xPlacePowerSeriesMap k
      (algebraMap k[X] (Ring (X : k[X])) X)) := by
    rw [xPlacePowerSeriesMap_X]
    exact PowerSeries.X_irreducible
  have hdvr := DVR.residue_restrict_apply (xPlacePowerSeriesMap k)
    (algebraMap (RatFunc k) (LaurentSeries k)) (xPlacePowerSeriesMap_fraction k)
    (irreducible_polynomial (X : k[X])) hirr n x
  have hsquare : PowerSeries.residueFieldOfPowerSeries.toRingHom.comp
      (IsLocalRing.ResidueField.map (xPlacePowerSeriesMap k)) =
        (InfinityResidue.rootXEquiv k).toRingHom.comp
          (residueEquiv (X : k[X])).toRingHom := by
    apply RingHom.ext
    exact xPlacePowerSeriesMap_residue k
  rw [residueAt_eq_dvr, LinearMap.comp_apply, ← hdvr]
  change ((MilnorK.map n (InfinityResidue.rootXEquiv k).toRingHom).comp
    (MilnorK.map n (residueEquiv (X : k[X])).toRingHom)) _ =
      ((MilnorK.map n PowerSeries.residueFieldOfPowerSeries.toRingHom).comp
        (MilnorK.map n (IsLocalRing.ResidueField.map (xPlacePowerSeriesMap k)))) _
  rw [← MilnorK.map_comp, ← MilnorK.map_comp, hsquare]

end MilnorK.PolynomialResidue
