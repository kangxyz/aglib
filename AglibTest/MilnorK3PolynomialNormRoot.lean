/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.PolynomialNormRoot
import Mathlib.Algebra.CharP.Two
import Lean.Util.CollectAxioms

/-!
# Actual polynomial root-norm consumers and rejecting axiom audit

These consumers expose the original tensor/Steinberg source and target,
the actual two-place residue vector, the infinity sign, and agreement with
the ordinary determinant norm. All statements hold over arbitrary fields.
-/

open Polynomial
open MilnorK.K2 MilnorK.K3
open MilnorK.K3.PolynomialResidue
open MilnorK.K3.PolynomialNorm

noncomputable section

namespace AglibTest.MilnorK3PolynomialNormRoot

variable {k : Type*} [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- The domain is the original quotient over the original polynomial algebra. -/
theorem actual_original_source (p : MonicIrreducible k) :
    MilnorK.K2.Group (AdjoinRoot p.val) =
      (TensorProduct ℤ (Additive (AdjoinRoot p.val)ˣ) (Additive (AdjoinRoot p.val)ˣ) ⧸
        steinbergSpan (AdjoinRoot p.val)) := rfl

/-- The codomain is the original base-field Milnor K₂ quotient. -/
theorem actual_original_target :
    MilnorK.K2.Group k = (TensorProduct ℤ (Additive kˣ) (Additive kˣ) ⧸ steinbergSpan k) := rfl

/-- The root unit is literally the original quotient class of the variable. -/
theorem literal_primitive_root (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) :
    (rootUnit p hp0 : AdjoinRoot p.val) = AdjoinRoot.mk p.val X := rfl

/-- The actual determinant norm formula does not even require irreducibility. -/
theorem ordinary_determinant_norm (p : k[X]) (hp : p.Monic) :
    Algebra.norm k (AdjoinRoot.root p) = (-1) ^ p.natDegree * p.coeff 0 :=
  AdjoinRoot.norm_root p hp

/-- At the genuine finite places, all residues except `p` and `X` vanish. -/
theorem actual_two_place_residue [DecidableEq (MonicIrreducible k)]
    (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) (b : kˣ) :
    totalResidue (symbol3 (polynomialUnit p.val p.property.2.ne_zero)
      (InfinityResidue.variableUnit k) (InfinityResidue.constantUnit k b)) =
      DFinsupp.single p (symbol (rootUnit p hp0)
        (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) -
      DFinsupp.single (variablePlace k)
        (MilnorK.K2.map (algebraMap k (AdjoinRoot (variablePlace k).val))
          (symbol (constantCoeffUnit p hp0) b)) :=
  totalResidue_polynomial_variable_constant p hp0 b

/-- The infinity contribution keeps the sign symbol and full polynomial degree. -/
theorem actual_infinity_sign (p : k[X]) (hp : p.Monic) (b : kˣ) :
    InfinityResidue.residue k (symbol3 (polynomialUnit p hp.ne_zero)
      (InfinityResidue.variableUnit k) (InfinityResidue.constantUnit k b)) =
      p.natDegree • symbol (-1) b :=
  residue_polynomial_variable_constant p hp b

/-- The actual polynomial Milnor norm agrees with the determinant norm of its
original root, with an arbitrary unit from the original base field. -/
theorem root_constant_norm (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) (b : kˣ) :
    polynomialNorm p (symbol (rootUnit p hp0)
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      symbol (Units.map (Algebra.norm k) (rootUnit p hp0)) b :=
  polynomialNorm_root_constant p hp0 b

/-- The same computation explicitly retains the determinant sign in the unit. -/
theorem root_constant_signed_coefficient
    (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) (b : kˣ) :
    polynomialNorm p (symbol (rootUnit p hp0)
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      symbol ((-1) ^ p.val.natDegree * Units.mk0 (p.val.coeff 0) hp0) b :=
  polynomialNorm_root_constant_coefficient p hp0 b

/-- The nonzero coefficient hypothesis excludes collision of the two finite places. -/
theorem finite_places_distinct (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) :
    p ≠ variablePlace k := ne_variablePlace p hp0

/-- In characteristic two the actual sign term vanishes without dividing by two. -/
theorem characteristic_two_infinity [CharP k 2] (p : k[X]) (hp : p.Monic) (b : kˣ) :
    InfinityResidue.residue k (symbol3 (polynomialUnit p hp.ne_zero)
      (InfinityResidue.variableUnit k) (InfinityResidue.constantUnit k b)) = 0 := by
  have hs : (-1 : kˣ) = 1 := by
    apply Units.ext
    exact CharTwo.neg_eq (1 : k)
  rw [residue_polynomial_variable_constant p hp b, hs, symbol_one_left, nsmul_zero]

/-- The root formula stays valid in characteristic two with its ordinary determinant norm. -/
theorem characteristic_two_root_norm [CharP k 2]
    (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) (b : kˣ) :
    polynomialNorm p (symbol (rootUnit p hp0)
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      symbol (constantCoeffUnit p hp0) b := by
  have hs : (-1 : kˣ) = 1 := by
    apply Units.ext
    exact CharTwo.neg_eq (1 : k)
  rw [polynomialNorm_root_constant_coefficient, hs, one_pow, one_mul]

end AglibTest.MilnorK3PolynomialNormRoot

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.RingTheory.AdjoinRootNormEvaluation,
    `Aglib.RingTheory.AdjoinRootNormRoot,
    `Aglib.RingTheory.PolynomialLocalResidue]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "The polynomial norm/root audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue,
    `Motivic.Aglib.FieldTheory.RatFuncInversion, `Motivic.Aglib.FieldTheory.RatFuncReverse,
    `Motivic.Aglib.RingTheory.AdjoinRootNormEvaluation,
    `Motivic.Aglib.RingTheory.AdjoinRootNormRoot]
  let consumerPrefix := `AglibTest.MilnorK3PolynomialNormRoot
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
        throwError "Polynomial norm/root declaration {name} is absent from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃, polynomial local residue, determinant root norm, \
    rational inversion/reversal, \
    and consumer declarations, including private helpers: only standard Lean logical foundations."
