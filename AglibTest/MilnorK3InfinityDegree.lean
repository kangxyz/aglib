/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.InfinityDegree
import Lean.Util.CollectAxioms

/-!
# Actual polynomial-degree residue consumers and rejecting axiom audit

These tests consume the arbitrary-field formula in the original Milnor K₃/K₂
quotients, including nonzero constants and nonmonic monomials. The positive
finite-place normalization and negative infinity normalization are retained
separately. Legacy imports include private implementation helpers in the audit.
-/

open Polynomial
open MilnorK.K2 MilnorK.K3
open MilnorK.K3.PolynomialResidue
open MilnorK.K3.InfinityResidue

noncomputable section

namespace AglibTest.MilnorK3InfinityDegree

variable {k : Type*} [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- The source is the original degree-three tensor/Steinberg quotient. -/
theorem actual_source :
    MilnorK.K3.Group (RatFunc k) = (TensorProduct ℤ (Additive (RatFunc k)ˣ) (MilnorK.K2.Group (RatFunc k)) ⧸
      R3 (RatFunc k)) := rfl

/-- The target remains the original base-field Milnor K₂ quotient. -/
theorem actual_original_target :
    MilnorK.K2.Group k = (TensorProduct ℤ (Additive kˣ) (Additive kˣ) ⧸ steinbergSpan k) := rfl

/-- Inversion is an equality of actual rational functions, also for zero or constants. -/
theorem literal_polynomial_inversion (p : k[X]) :
    RatFunc.inversion k (algebraMap k[X] (RatFunc k) p) =
      (RatFunc.X⁻¹ : RatFunc k) ^ p.natDegree *
        algebraMap k[X] (RatFunc k) p.reverse :=
  RatFunc.inversion_algebraMap_reverse k p

/-- The reverse has a genuinely nonzero coefficient at zero. -/
theorem reverse_constant_coefficient_nonzero (p : k[X]) (hp : p ≠ 0) :
    p.reverse.coeff 0 ≠ 0 := by
  rw [coeff_zero_reverse]
  exact leadingCoeff_ne_zero.mpr hp

/-- The finite residue of the reversed polynomial and constant units is zero. -/
theorem reverse_finite_vanishing (p : k[X]) (hp : p ≠ 0) (a b : kˣ) :
    residueAt (X : k[X])
      (symbol3 (polynomialUnit p.reverse (reverse_eq_zero.not.mpr hp))
        (Units.map (algebraMap k (RatFunc k)).toMonoidHom a)
        (Units.map (algebraMap k (RatFunc k)).toMonoidHom b)) = 0 :=
  residueAt_reverse_constants k p hp a b

/-- The actual finite place `X` has the positive first-slot normalization. -/
theorem finite_variable_positive (a b : kˣ) :
    MilnorK.K2.map (rootXEquiv k).toRingHom
      (residueAt (X : k[X])
        (symbol3 (polynomialUnit X X_ne_zero) (constantUnit k a) (constantUnit k b))) =
      symbol a b := by
  rw [← polynomialUnit_constant k a, ← polynomialUnit_constant k b,
    residueAt_polynomial_units X (C (a : k)) (C (b : k))
      (C_ne_zero.mpr a.ne_zero) (C_ne_zero.mpr b.ne_zero)
      (not_dvd_constant k a) (not_dvd_constant k b),
    MilnorK.K2.map_symbol,
    rootXEquiv_quotientUnit_constant, rootXEquiv_quotientUnit_constant]

/-- The formula concerns literal rational-function units and original base-field symbols. -/
theorem literal_polynomial_degree (p : k[X]) (hp : p ≠ 0) (a b : kˣ) :
    residue k
      (symbol3 (Units.mk0 (algebraMap k[X] (RatFunc k) p) (RatFunc.algebraMap_ne_zero hp))
        (Units.map (algebraMap k (RatFunc k)).toMonoidHom a)
        (Units.map (algebraMap k (RatFunc k)).toMonoidHom b)) =
      -(p.natDegree : ℤ) • symbol a b :=
  residue_polynomial_constants k p hp a b

/-- Degree zero is included: every nonzero constant polynomial gives zero. -/
theorem nonzero_constant_degree_zero (c a b : kˣ) :
    residue k
      (symbol3 (polynomialUnit (C (c : k)) (C_ne_zero.mpr c.ne_zero))
        (constantUnit k a) (constantUnit k b)) = 0 := by
  simpa only [natDegree_C, Nat.cast_zero, neg_zero, zero_smul] using
    residue_polynomial_constants k (C (c : k)) (C_ne_zero.mpr c.ne_zero) a b

/-- The degree formula has the negative infinity sign already at the variable. -/
theorem infinity_variable_negative (a b : kˣ) :
    residue k
      (symbol3 (polynomialUnit (X : k[X]) X_ne_zero)
        (constantUnit k a) (constantUnit k b)) = -symbol a b := by
  simpa only [natDegree_X, Nat.cast_one, neg_smul, one_smul] using
    residue_polynomial_constants k X X_ne_zero a b

/-- Arbitrary nonmonic monomials retain their full negative degree, including exponent zero. -/
theorem nonmonic_monomial_degree (c a b : kˣ) (n : ℕ) :
    residue k
      (symbol3 (polynomialUnit (C (c : k) * X ^ n)
        (mul_ne_zero (C_ne_zero.mpr c.ne_zero) (pow_ne_zero n X_ne_zero)))
        (constantUnit k a) (constantUnit k b)) = -(n : ℤ) • symbol a b := by
  simpa only [natDegree_C_mul_X_pow n (c : k) c.ne_zero] using
    residue_polynomial_constants k (C (c : k) * X ^ n)
      (mul_ne_zero (C_ne_zero.mpr c.ne_zero) (pow_ne_zero n X_ne_zero)) a b

end AglibTest.MilnorK3InfinityDegree

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.RingTheory.PolynomialLocalResidue]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "The infinity degree audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue,
    `Motivic.Aglib.FieldTheory.RatFuncInversion, `Motivic.Aglib.FieldTheory.RatFuncReverse]
  let consumerPrefix := `AglibTest.MilnorK3InfinityDegree
  let isLibrary (name : Name) : Bool := libraryPrefixes.any (·.isPrefixOf name)
  let selectedDeclaration (name : Name) : Bool :=
    let libraryOrigin := match env.getModuleIdxFor? name with
      | some index => isLibraryModule env.header.moduleNames[index.toNat]!
      | none => false
    libraryOrigin || isLibrary name || consumerPrefix.isPrefixOf name
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for i in [:env.header.moduleNames.size] do
    let libraryOrigin := isLibraryModule env.header.moduleNames[i]!
    for name in env.header.moduleData[i]!.constNames do
      if libraryOrigin || isLibrary name then
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    if selected name then
      unless (env.checked.get.find? name).isSome do
        throwError "Infinity degree declaration {name} is absent from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃, polynomial local residue, rational inversion/reversal, \
    and consumer declarations, including private helpers: only standard Lean logical foundations."
