/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Polynomial.LaurentSeries
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Direct consumers of the actual polynomial-to-Laurent-series residue square. -/

open Polynomial Polynomial.LocalResidue
open MilnorK MilnorK.PolynomialResidue
open scoped RatFunc

namespace AglibTest.GeneralMilnorPolynomialResidueLaurentSeries

variable (k : Type*) [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- Equality of the actual all-degree maps, not only a selected symbol formula. -/
theorem actual_completion_square (n : ℕ) :
    (map n (InfinityResidue.rootXEquiv k).toRingHom).comp (residueAt (X : k[X]) n) =
      ((map n PowerSeries.residueFieldOfPowerSeries.toRingHom).comp
        (DVR.residue (PowerSeries k) (LaurentSeries k) n)).comp
          (map (n + 1) (algebraMap (RatFunc k) (LaurentSeries k))) := by
  apply LinearMap.ext
  intro x
  exact residueAt_X_eq_laurentSeries_residue k n x

/-- The empty-prefix degree-one normalization remains positive at the finite
place `X`, excluding an accidental infinity-sign convention. -/
theorem completion_variable_degree_one :
    zeroEquiv k (map 0 PowerSeries.residueFieldOfPowerSeries.toRingHom
      (DVR.residue (PowerSeries k) (LaurentSeries k) 0
        (map 1 (algebraMap (RatFunc k) (LaurentSeries k))
          (symbol (Fin.snoc Fin.elim0 (polynomialUnit (X : k[X]) X_ne_zero)))))) = 1 := by
  rw [← residueAt_X_eq_laurentSeries_residue]
  have h := residueAt_polynomial_units (X : k[X]) 0 Fin.elim0
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have htuple : (fun i : Fin 0 => polynomialUnit (Fin.elim0 i) (Fin.elim0 i)) =
      (Fin.elim0 : SymbolTuple (RatFunc k) 0) := Subsingleton.elim _ _
  rw [htuple] at h
  rw [h, map_symbol, zeroEquiv_symbol]

/-- The same all-class theorem admits a concrete positive-characteristic field. -/
theorem completion_characteristic_two (n : ℕ) (x : K (RatFunc (ZMod 2)) (n + 1)) :
    map n (InfinityResidue.rootXEquiv (ZMod 2)).toRingHom
        (residueAt (X : (ZMod 2)[X]) n x) =
      map n PowerSeries.residueFieldOfPowerSeries.toRingHom
        (DVR.residue (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) n
          (map (n + 1) (algebraMap (RatFunc (ZMod 2)) (LaurentSeries (ZMod 2))) x)) :=
  residueAt_X_eq_laurentSeries_residue (ZMod 2) n x

end AglibTest.GeneralMilnorPolynomialResidueLaurentSeries

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `Polynomial.LocalResidue.xPlacePowerSeriesMap,
    `Polynomial.LocalResidue.xPlacePowerSeriesMap_isLocalHom,
    `Polynomial.LocalResidue.xPlacePowerSeriesMap_fraction,
    `Polynomial.LocalResidue.xPlacePowerSeriesMap_residue,
    `MilnorK.PolynomialResidue.residueAt_X_eq_laurentSeries_residue,
    `AglibTest.GeneralMilnorPolynomialResidueLaurentSeries.actual_completion_square,
    `AglibTest.GeneralMilnorPolynomialResidueLaurentSeries.completion_variable_degree_one,
    `AglibTest.GeneralMilnorPolynomialResidueLaurentSeries.completion_characteristic_two]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Checked the actual Laurent-series residue square: standard axioms only."
