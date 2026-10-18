/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.CompleteScalarBranch

/-!
# Actual scalar-branch diagram consumers

These tests keep the original polynomial, its literal coefficient branch,
and the two canonical integral-closure maps. No singleton-branch hypothesis
or auxiliary norm-residue premise is used.
-/

@[expose] public noncomputable section

namespace AglibTest.GeneralMilnorCompleteScalarBranch

open Polynomial Polynomial.LocalResidue AdjoinRoot IsLocalRing
open MilnorK MilnorK.PolynomialResidue
open MilnorK.PolynomialNorm.CompleteScalarBranch
open IsDiscreteValuationRing.IntegralClosureTower

attribute [local instance] AdjoinRoot.scalarBranchAlgebra closureAlgebra

section Maps

variable (R F L : Type*) [CommRing R] [Field F] [Field L]
  [Algebra F L] [Algebra R F] [Algebra R L] [IsScalarTower R F L]
  (p : MonicIrreducible F) (r : IrreducibleBranch (p.val.map (algebraMap F L)))

/-- The old-root map retains the exact quotient map, not an abstract embedding. -/
theorem actual_oldRoot_map (s : integralClosure R (AdjoinRoot p.val)) :
    algebraMap (integralClosure R (AdjoinRoot r.val.val)) (AdjoinRoot r.val.val)
      (algebraMap (integralClosure R (AdjoinRoot p.val))
        (integralClosure R (AdjoinRoot r.val.val)) s) =
      adjoinRootMap (algebraMap F L) p.val r.val.val r.property
        (algebraMap (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) s) :=
  oldRoot_closureMap_apply R p r s

/-- The literal upper ring is already the closure over the actual old-root ring. -/
theorem actual_oldRoot_closure :
    IsIntegralClosure (integralClosure R (AdjoinRoot r.val.val))
      (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot r.val.val) :=
  oldRoot_isIntegralClosure R p r

omit [Algebra R F] [IsScalarTower R F L] in
/-- The same literal upper ring is also the closure over the actual coefficient ring. -/
theorem actual_coefficient_closure :
    IsIntegralClosure (integralClosure R (AdjoinRoot r.val.val))
      (integralClosure R L) (AdjoinRoot r.val.val) :=
  coefficient_isIntegralClosure R p r

end Maps

section Finite

variable (R F L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [FiniteDimensional F L]
  (p : MonicIrreducible F) (r : IrreducibleBranch (p.val.map (algebraMap F L)))

/-- Both actual upper ring extensions are finite, without assuming coprime degrees. -/
theorem actual_both_upper_finite :
    Module.Finite (integralClosure R (AdjoinRoot p.val))
        (integralClosure R (AdjoinRoot r.val.val)) ∧
      Module.Finite (integralClosure R L) (integralClosure R (AdjoinRoot r.val.val)) :=
  ⟨oldRoot_finite R F L p r, coefficient_finite R F L p r⟩

end Finite

open Lean in
run_cmd do
  for name in #[``MilnorK.PolynomialNorm.CompleteScalarBranch.branch_algebraMap_eq,
      ``MilnorK.PolynomialNorm.CompleteScalarBranch.baseBranchTower,
      ``MilnorK.PolynomialNorm.CompleteScalarBranch.oldRoot_closureMap_apply,
      ``MilnorK.PolynomialNorm.CompleteScalarBranch.coefficient_closureMap_apply,
      ``MilnorK.PolynomialNorm.CompleteScalarBranch.oldRoot_isIntegralClosure,
      ``MilnorK.PolynomialNorm.CompleteScalarBranch.coefficient_isIntegralClosure,
      ``MilnorK.PolynomialNorm.CompleteScalarBranch.oldRoot_isLocalHom,
      ``MilnorK.PolynomialNorm.CompleteScalarBranch.coefficient_isLocalHom,
      ``MilnorK.PolynomialNorm.CompleteScalarBranch.oldRoot_finite,
      ``MilnorK.PolynomialNorm.CompleteScalarBranch.coefficient_finite,
      ``residue_finiteExtensionNorm_complete_scalarBranch_of_pGroup,
      ``actual_oldRoot_map, ``actual_oldRoot_closure, ``actual_coefficient_closure,
      ``actual_both_upper_finite] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Every actual complete scalar-branch square uses only standard foundations."

end AglibTest.GeneralMilnorCompleteScalarBranch
