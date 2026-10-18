/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.Compatibility
public import Lean.Util.CollectAxioms

/-!
# Consumers of the full polynomial norm presentation comparison

The test statements retain arbitrary fields and arbitrary quotient classes.
They exercise every finite residue, infinity, arbitrary finite residue vectors,
and individual polynomial norm components, without root-generation hypotheses.
-/

@[expose] public noncomputable section

open Polynomial
open MilnorK MilnorK.PolynomialResidue MilnorK.PolynomialNorm

namespace AglibTest.MilnorKPolynomialNormCompatibility

variable {k : Type*} [Field k]

/-- Every actual finite residue, with no characteristic restriction. -/
theorem actual_finite_residue (p : k[X]) [Fact (Irreducible p)]
    (x : K (RatFunc k) 3) :
    twoEquiv (AdjoinRoot p) (residueAt p 2 x) =
      MilnorK.K3.PolynomialResidue.residueAt p (threeEquiv (RatFunc k) x) :=
  twoEquiv_residueAt p x

/-- The infinity comparison holds on arbitrary rational-function Milnor classes. -/
theorem actual_infinity (x : K (RatFunc k) 3) :
    twoEquiv k (MilnorK.InfinityResidue.residue k 2 x) =
      MilnorK.K3.InfinityResidue.residue k (threeEquiv (RatFunc k) x) :=
  twoEquiv_infinityResidue x

/-- Arbitrary genuine finite residue vectors are included. -/
theorem actual_total (y : Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) 2) :
    twoEquiv k (totalNorm 2 y) = MilnorK.K3.PolynomialNorm.totalNorm (residueTwoMap y) :=
  twoEquiv_totalNorm y

/-- Every actual polynomial-presentation norm agrees, on every input class. -/
theorem actual_component (p : MonicIrreducible k) (x : K (AdjoinRoot p.val) 2) :
    twoEquiv k (polynomialNorm 2 p x) =
      MilnorK.K3.PolynomialNorm.polynomialNorm p (twoEquiv (AdjoinRoot p.val) x) :=
  twoEquiv_polynomialNorm p x

/-- An old quotient input can also be transported back with no extra hypothesis. -/
theorem actual_old_input (p : MonicIrreducible k) (x : MilnorK.K2.Group (AdjoinRoot p.val)) :
    polynomialNorm 2 p ((twoEquiv (AdjoinRoot p.val)).symm x) =
      (twoEquiv k).symm (MilnorK.K3.PolynomialNorm.polynomialNorm p x) := by
  apply (twoEquiv k).injective
  rw [twoEquiv_polynomialNorm, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- The comparison is available as an actual equality of linear composites. -/
theorem actual_square (p : MonicIrreducible k) :
    (twoEquiv k).toLinearMap.comp (polynomialNorm 2 p) =
      (MilnorK.K3.PolynomialNorm.polynomialNorm p).comp
        (twoEquiv (AdjoinRoot p.val)).toLinearMap :=
  twoEquiv_polynomialNorm_square p

open Lean in
run_cmd do
  for name in #[``twoEquiv_residueAt, ``twoEquiv_infinityResidue,
      ``residueTwoMap_totalResidue, ``twoEquiv_totalNorm, ``twoEquiv_polynomialNorm,
      ``twoEquiv_polynomialNorm_square, ``actual_finite_residue, ``actual_infinity,
      ``actual_total, ``actual_component, ``actual_old_input, ``actual_square] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Full degree-two norm compatibility uses only standard Lean logical foundations."

end AglibTest.MilnorKPolynomialNormCompatibility
