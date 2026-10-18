/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.FiniteExtension.BaseChange
import Aglib.RingTheory.AdjoinRootNestedBaseChange
import Lean.Util.CollectAxioms

/-! Full actual finite-field branch sum and literal tensor coordinates. -/

namespace AglibTest.GeneralMilnorFiniteExtensionNormBaseChange

open MilnorK Polynomial PolynomialResidue PolynomialNorm AdjoinRoot
open scoped TensorProduct

/-- Original-field base change retains every branch and original coefficient map. -/
theorem actual_norm_basechange {k S E : Type*} [Field k] [CharZero k] [Field S]
    [CharZero S] [Field E] [Algebra k S] [Algebra k E] [FiniteDimensional k E]
    (p : MonicIrreducible k) (ε : AdjoinRoot p.val ≃ₐ[k] E)
    [Fintype (IrreducibleBranch (p.val.map (algebraMap k S)))] (n : ℕ) (x : K E n) :
    map n (algebraMap k S) (finiteExtensionNorm k E n x) =
      ∑ r : IrreducibleBranch (p.val.map (algebraMap k S)),
        polynomialNorm n r.val
          (map n ((Polynomial.LocalResidue.adjoinRootMap (algebraMap k S)
            p.val r.val.val r.property).comp ε.symm.toRingHom) x) := by
  have h := finiteExtensionNorm_restrict_presentation (S := S) E p ε n x
  simpa only [finiteExtensionNorm_adjoinRoot] using h

attribute [local instance] AdjoinRoot.scalarBranchAlgebra

/-- Tensor associativity keeps the original two entries in every nested factor. -/
theorem actual_nested_coordinate {k S E : Type*} [Field k] [CharZero k] [Field S]
    [Algebra k S] (p : k[X]) (hp : p.Monic) [Fact (Irreducible p)]
    [Field E] [Algebra (AdjoinRoot p) E] [Algebra k E]
    [IsScalarTower k (AdjoinRoot p) E] (a : E) (b : S)
    (r : IrreducibleBranch (p.map (algebraMap k S))) :
    nestedScalarProductEquiv p hp E (a ⊗ₜ[k] b) r =
      a ⊗ₜ[AdjoinRoot p] algebraMap S (AdjoinRoot r.val.val) b :=
  nestedScalarProductEquiv_tmul p hp E a b r

end AglibTest.GeneralMilnorFiniteExtensionNormBaseChange

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.AdjoinRootNormalScalarBranch,
    `Aglib.FieldTheory.AdjoinRootSplitBranchEmbedding,
    `Aglib.FieldTheory.CoprimeIrreducibility,
    `Aglib.FieldTheory.FiniteCoprimeSplitting,
    `Aglib.FieldTheory.PGroupNormalSubfield,
    `Aglib.FieldTheory.PGroupNormalSubfieldEmbedding,
    `Aglib.FieldTheory.PrimeNormalScalarDichotomy,
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.FieldTheory.RatFuncTranslation,
    `Aglib.FieldTheory.RationalCoefficientRoot,
    `Aglib.FieldTheory.SylowFixedField,
    `Aglib.RingTheory.AdjoinRootBranchProduct,
    `Aglib.RingTheory.AdjoinRootCoefficientEquiv,
    `Aglib.RingTheory.AdjoinRootNestedBaseChange,
    `Aglib.RingTheory.AdjoinRootScalarBranches,
    `Aglib.RingTheory.AdjoinRootTensorBranches,
    `Aglib.RingTheory.AdjoinRootTowerBranch,
    `Aglib.RingTheory.AdjoinRootTowerBranchChange,
    `Aglib.RingTheory.CompleteDVRExtension,
    `Aglib.RingTheory.CompleteDVRIntegralClosureTower,
    `Aglib.RingTheory.DVRNormResidueUnit,
    `Aglib.RingTheory.DVRNormValuation,
    `Aglib.RingTheory.DVRPrimeUniformizerNorm,
    `Aglib.RingTheory.DVRRamificationDegree,
    `Aglib.RingTheory.DVRUniformizerBinomial,
    `Aglib.RingTheory.DVRUniformizerNorm,
    `Aglib.RingTheory.FiniteAlgebraNormLength,
    `Aglib.RingTheory.FiniteLength.FiniteAlgebraFiber,
    `Aglib.RingTheory.FiniteLength.FiniteAlgebraLength,
    `Aglib.RingTheory.FiniteLength.Support,
    `Aglib.RingTheory.HenselianPrincipalRoots,
    `Aglib.RingTheory.HenselianUniformizerNormalization,
    `Aglib.RingTheory.Length.ExactSequence,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Support,
    `Aglib.RingTheory.PolynomialFiberNorm,
    `Aglib.RingTheory.PolynomialLocalResidue,
    `Aglib.RingTheory.PolynomialPlaceContraction,
    `Aglib.RingTheory.PolynomialResidueBaseChange,
    `Aglib.RingTheory.PowerSeriesConstantClosure,
    `Aglib.RingTheory.PrimeFiltration.Basic,
    `Aglib.RingTheory.PrimeFiltration.Length,
    `Aglib.RingTheory.PrimeFiltration.Multiplicity,
    `Aglib.RingTheory.PrimeFiltration.Primes,
    `Aglib.RingTheory.PrimeFiltration.Support,
    `Aglib.RingTheory.ScalarHomology.Basic]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `MilnorK,
    `AglibTest.GeneralMilnorFiniteExtensionNormBaseChange]
  let selectedDeclaration (name : Name) := prefixes.any (·.isPrefixOf name)
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} actual branch base-change and tensor-coordinate declarations: \
    standard axioms only."
