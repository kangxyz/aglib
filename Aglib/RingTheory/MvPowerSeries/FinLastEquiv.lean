/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.TriangularSpecialization
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Isolating the last formal variable

The native `finSuccEquiv` isolates the first variable. Swapping it with the
last variable gives an explicit equivalence suited to positive lexicographic
weight normalization. Mapping every coefficient to its constant coefficient
is exactly restriction to the last coordinate axis.
-/

@[expose] public section

namespace MvPowerSeries

variable (R : Type*) [CommRing R]

/-- The iterated-series equivalence whose outer variable is the last variable. -/
noncomputable def finLastEquiv (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] PowerSeries (MvPowerSeries (Fin n) R) :=
  (renameEquiv R (Equiv.swap 0 (Fin.last n))).trans (finSuccEquiv R n)

variable {R}

/-- Constant coefficients of the iterated coefficients are the pure last-axis coefficients. -/
theorem constantCoeff_coeff_finLastEquiv (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) R) (k : ℕ) :
    constantCoeff (PowerSeries.coeff k (finLastEquiv R n f)) =
      coeff (Finsupp.single (Fin.last n) k) f := by
  classical
  change constantCoeff (PowerSeries.coeff k (finSuccEquiv R n
    (rename (Equiv.swap 0 (Fin.last n)) f))) = _
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_coeff_finSuccEquiv,
    Finsupp.cons_zero_eq_single_zero]
  have h := coeff_embDomain_rename (Equiv.swap 0 (Fin.last n)).toEmbedding
    f (Finsupp.single (Fin.last n) k)
  simpa only [Finsupp.embDomain_single, Equiv.coe_toEmbedding,
    Equiv.swap_apply_right] using h

/-- Passing to constant coefficients after isolating the last variable is axis restriction. -/
theorem map_constantCoeff_finLastEquiv (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) R) :
    PowerSeries.map (constantCoeff : MvPowerSeries (Fin n) R →+* R)
      (finLastEquiv R n f) = killCompl (axisEmbedding (Fin.last n)) f := by
  apply PowerSeries.ext
  intro k
  rw [PowerSeries.coeff_map, constantCoeff_coeff_finLastEquiv]
  change coeff (Finsupp.single (Fin.last n) k) f =
    coeff (Finsupp.single () k) (killCompl (axisEmbedding (Fin.last n)) f)
  rw [coeff_killCompl, Finsupp.embDomain_single]
  rfl

end MvPowerSeries
