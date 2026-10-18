/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Polynomial.LinearLaurentSeries
import Lean.Util.CollectAxioms

/-! Literal linear uniformizers and the original all-class finite residue in the
native Laurent-series completion. -/

open Polynomial Polynomial.LocalResidue
open MilnorK MilnorK.PolynomialResidue

namespace AglibTest.GeneralMilnorPolynomialResidueLinearLaurentSeries

variable {k : Type*} [Field k]

local instance (a : k) : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩

/-- The original linear polynomial unit is sent to the native complete-DVR
uniformizer itself, not merely an associated unit. -/
theorem actual_uniformizer (a : k) :
    Units.map (linearPlaceLaurentSeriesMap a).toMonoidHom
      (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero) =
        MilnorK.K2.DVR.uniformizer
          (R := PowerSeries k) (K := LaurentSeries k) PowerSeries.X_irreducible := by
  apply Units.ext
  change linearPlaceLaurentSeriesMap a (algebraMap k[X] (RatFunc k) (X - C a)) =
    algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X
  rw [linearPlaceLaurentSeriesMap_polynomial, linearPlacePolynomialMap_uniformizer]

/-- Finite-place degree-one normalization stays positive after translation. -/
theorem completion_linear_degree_one (a : k) :
    zeroEquiv k (map 0 PowerSeries.residueFieldOfPowerSeries.toRingHom
      (DVR.residue (PowerSeries k) (LaurentSeries k) 0
        (map 1 (linearPlaceLaurentSeriesMap a)
          (symbol (Fin.snoc Fin.elim0
            (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero)))))) = 1 := by
  rw [← residueAt_linear_eq_laurentSeries_residue]
  have h := residueAt_polynomial_units (X - C a) 0 Fin.elim0
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have htuple : (fun i : Fin 0 => polynomialUnit (Fin.elim0 i) (Fin.elim0 i)) =
      (Fin.elim0 : SymbolTuple (RatFunc k) 0) := Subsingleton.elim _ _
  rw [htuple] at h
  rw [h, map_symbol, zeroEquiv_symbol]

/-- Every original finite residue is recovered on arbitrary Milnor classes,
with the actual coefficient map and translated rational-function map visible. -/
theorem original_finite_residue [CharZero k]
    (p : k[X]) [Fact (Irreducible p)] (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    residueAt p n x =
      map n PowerSeries.residueFieldOfPowerSeries.toRingHom
        (DVR.residue (PowerSeries (AdjoinRoot p)) (LaurentSeries (AdjoinRoot p)) n
          (map (n + 1) ((linearPlaceLaurentSeriesMap (AdjoinRoot.root p)).comp
            (fractionMap (algebraMap k (AdjoinRoot p)))) x)) :=
  residueAt_eq_root_laurentSeries_residue p n x

end AglibTest.GeneralMilnorPolynomialResidueLinearLaurentSeries

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `Polynomial.LocalResidue.linearPlacePowerSeriesMap,
    `Polynomial.LocalResidue.linearPlacePowerSeriesMap_isLocalHom,
    `Polynomial.LocalResidue.linearPlaceLaurentSeriesMap,
    `Polynomial.LocalResidue.linearPlacePowerSeriesMap_fraction,
    `Polynomial.LocalResidue.linearPlacePowerSeriesMap_residue,
    `MilnorK.PolynomialResidue.residueAt_linear_eq_laurentSeries_residue,
    `MilnorK.PolynomialResidue.residueAt_eq_root_laurentSeries_residue,
    `AglibTest.GeneralMilnorPolynomialResidueLinearLaurentSeries.actual_uniformizer,
    `AglibTest.GeneralMilnorPolynomialResidueLinearLaurentSeries.completion_linear_degree_one,
    `AglibTest.GeneralMilnorPolynomialResidueLinearLaurentSeries.original_finite_residue]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Checked the original finite residue in Laurent series: standard axioms only."
