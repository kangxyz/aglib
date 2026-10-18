/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Polynomial.CompleteCoefficient
import Lean.Util.CollectAxioms

/-! The original upper rational map and actual integral closure, with no
postulated local map, residue isomorphism or compatibility assumption. -/

open Polynomial Polynomial.LocalResidue
open MilnorK MilnorK.PolynomialResidue
open MilnorK.PolynomialNorm
open MilnorK.PolynomialNorm.CompleteCoefficientResidue
open PowerSeries.ConstantClosure

namespace AglibTest.GeneralMilnorPolynomialResidueCompleteCoefficient

variable {k : Type*} [Field k] [CharZero k] (p : MonicIrreducible k)

local instance : Fact (Irreducible (X : (AdjoinRoot p.val)[X])) := ⟨irreducible_X⟩

/-- The localization sends the original rational variable to the literal
power-series parameter inside the actual integral closure. -/
theorem actual_local_uniformizer :
    upperLocalMap p (algebraMap (AdjoinRoot p.val)[X]
      (Ring (X : (AdjoinRoot p.val)[X])) X) =
        algebraMap (PowerSeries k) (Closure p) PowerSeries.X :=
  coefficientDVRLocalMap_X _ _ _ _ _

/-- The upper residue square uses exactly the field map already occurring in
the original polynomial norm's completion base change. -/
theorem original_completion_map_square (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (residueEquiv p).symm.toRingHom
      (DVR.residue (Closure p) (TopField p) n
        (map (n + 1) (rationalCompletionRootMap p (constantPolynomial p)
          (constantPolynomial_eq_rationalCoefficient_map p)) x)) =
        map n (InfinityResidue.rootXEquiv (AdjoinRoot p.val)).toRingHom
          (residueAt (X : (AdjoinRoot p.val)[X]) n x) := by
  rw [← upperFieldMap_eq_rationalCompletionRootMap]
  exact upper_residue_square p n x

end AglibTest.GeneralMilnorPolynomialResidueCompleteCoefficient

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `Polynomial.LocalResidue.coefficientDVRLocalMap,
    `Polynomial.LocalResidue.coefficientDVRLocalMap_isLocalHom,
    `Polynomial.LocalResidue.coefficientDVRLocalMap_fraction,
    `MilnorK.PolynomialNorm.rationalCoefficientLaurentMap,
    `MilnorK.PolynomialNorm.rationalCoefficientLaurentMap_C,
    `MilnorK.PolynomialNorm.rationalCoefficientLaurentMap_X,
    `MilnorK.PolynomialNorm.rationalCoefficientLaurentMap_fractionMap,
    `MilnorK.PolynomialNorm.CompleteCoefficientResidue.upperLocalMap,
    `MilnorK.PolynomialNorm.CompleteCoefficientResidue.upperLocalMap_fraction,
    `MilnorK.PolynomialNorm.CompleteCoefficientResidue.upper_residue_square,
    `AglibTest.GeneralMilnorPolynomialResidueCompleteCoefficient.actual_local_uniformizer,
    `AglibTest.GeneralMilnorPolynomialResidueCompleteCoefficient.original_completion_map_square]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Checked the actual upper complete-coefficient residue square: standard axioms only."
