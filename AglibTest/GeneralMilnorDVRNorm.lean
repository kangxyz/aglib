/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.FiniteExtension.DVR
import Lean.Util.CollectAxioms

/-! Original-field and original-branch norm-residue consumer and axiom audit. -/

noncomputable section

namespace AglibTest.GeneralMilnorDVRNorm
open MilnorK
open IsLocalRing AdicCompletion
open scoped TensorProduct

universe u
variable (R S F E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero (ResidueField R)]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E] [FiniteDimensional F E]


/-- Direct original-field consumer of every original valuation branch. -/
theorem actual_original_dvr_sum (n : ℕ) (x : K E (n + 1)) :
    letI := fun q : IdealBranch ((maximalIdeal R).map (algebraMap R S)) =>
      originalBranchFractionAlgebra S E q
    letI := fun q : IdealBranch ((maximalIdeal R).map (algebraMap R S)) =>
      originalBranchIsFractionRing S E q
    DVR.residue R F n (finiteExtensionNorm F E (n + 1) x) =
      ∑ q : IdealBranch ((maximalIdeal R).map (algebraMap R S)),
        finiteExtensionNorm (ResidueField R) (ResidueField (Localization.AtPrime q.val)) n
          (DVR.residue (Localization.AtPrime q.val) E n x) :=
  residue_finiteExtensionNorm_dvr R S F E n x

end AglibTest.GeneralMilnorDVRNorm

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.AdjoinRootMinpolyDegree,
    `Aglib.FieldTheory.AdjoinRootNormalScalarBranch,
    `Aglib.FieldTheory.AdjoinRootSplitBranchEmbedding,
    `Aglib.FieldTheory.CoprimeIrreducibility,
    `Aglib.FieldTheory.FieldCharpolyPower,
    `Aglib.FieldTheory.FiniteCoprimeSplitting,
    `Aglib.FieldTheory.PGroupNormalSubfield,
    `Aglib.FieldTheory.PGroupNormalSubfieldEmbedding,
    `Aglib.FieldTheory.PrimeNormalScalarDichotomy,
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.FieldTheory.RatFuncTranslation,
    `Aglib.FieldTheory.RationalCoefficientRoot,
    `Aglib.FieldTheory.ResidueMinpolyBranch,
    `Aglib.FieldTheory.SylowFixedField,
    `Aglib.FieldTheory.TensorCharpolyProduct,
    `Aglib.RingTheory.AdicCompletion.BranchBaseLocal,
    `Aglib.RingTheory.AdicCompletion.BranchFractionAlgebra,
    `Aglib.RingTheory.AdicCompletion.BranchFractionFinite,
    `Aglib.RingTheory.AdicCompletion.BranchUniformizer,
    `Aglib.RingTheory.AdicCompletion.ChineseRemainder,
    `Aglib.RingTheory.AdicCompletion.DedekindBranches,
    `Aglib.RingTheory.AdicCompletion.FiniteAlgebra,
    `Aglib.RingTheory.AdicCompletion.FiniteDedekindBranches,
    `Aglib.RingTheory.AdicCompletion.FractionBaseChange,
    `Aglib.RingTheory.AdicCompletion.FractionBranches,
    `Aglib.RingTheory.AdicCompletion.FractionTensorBranches,
    `Aglib.RingTheory.AdicCompletion.LocalCompletionsBase,
    `Aglib.RingTheory.AdicCompletion.Localization,
    `Aglib.RingTheory.AdicCompletion.OriginalBranchFractions,
    `Aglib.RingTheory.AdicCompletion.OriginalBranchResidues,
    `Aglib.RingTheory.AdicCompletion.Powers,
    `Aglib.RingTheory.AdicCompletion.ScalarExtension,
    `Aglib.RingTheory.AdicCompletion.SemilocalBranches,
    `Aglib.RingTheory.AdjoinRootBranchProduct,
    `Aglib.RingTheory.AdjoinRootCoefficientEquiv,
    `Aglib.RingTheory.AdjoinRootFieldProductBranches,
    `Aglib.RingTheory.AdjoinRootNestedBaseChange,
    `Aglib.RingTheory.AdjoinRootNestedBranches,
    `Aglib.RingTheory.AdjoinRootPiBranches,
    `Aglib.RingTheory.AdjoinRootScalarBranches,
    `Aglib.RingTheory.AdjoinRootTensorBranchProduct,
    `Aglib.RingTheory.AdjoinRootTensorBranches,
    `Aglib.RingTheory.AdjoinRootTowerBranch,
    `Aglib.RingTheory.AdjoinRootTowerBranchChange,
    `Aglib.RingTheory.CompleteDVRExtension,
    `Aglib.RingTheory.CompleteDVRIntegralClosureTower,
    `Aglib.RingTheory.DVRCharpolyBranchCount,
    `Aglib.RingTheory.DVRCharpolyResidue,
    `Aglib.RingTheory.DVRNormResidueUnit,
    `Aglib.RingTheory.DVRNormValuation,
    `Aglib.RingTheory.DVRPrimeUniformizerNorm,
    `Aglib.RingTheory.DVRRamificationDegree,
    `Aglib.RingTheory.DVRUniformizerBinomial,
    `Aglib.RingTheory.DVRUniformizerNorm,
    `Aglib.RingTheory.DiscreteValuationRing.FractionAway,
    `Aglib.RingTheory.DiscreteValuationRing.FractionBaseChange,
    `Aglib.RingTheory.DiscreteValuationRing.FractionPi,
    `Aglib.RingTheory.DiscreteValuationRing.IntegralFractionAway,
    `Aglib.RingTheory.FiniteAlgebraNormLength,
    `Aglib.RingTheory.FiniteLength.FiniteAlgebraFiber,
    `Aglib.RingTheory.FiniteLength.FiniteAlgebraLength,
    `Aglib.RingTheory.FiniteLength.Support,
    `Aglib.RingTheory.HenselianPrincipalRoots,
    `Aglib.RingTheory.HenselianUniformizerNormalization,
    `Aglib.RingTheory.IntegralTensorCharpolyProduct,
    `Aglib.RingTheory.IntermediateIntegralClosureTower,
    `Aglib.RingTheory.Length.ExactSequence,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Support,
    `Aglib.RingTheory.PolynomialFiberNorm,
    `Aglib.RingTheory.PolynomialLocalResidue,
    `Aglib.RingTheory.PolynomialPlaceContraction,
    `Aglib.RingTheory.PolynomialPowerFactorCount,
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
    `AglibTest.GeneralMilnorDVRNorm]
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
  logInfo m!"Checked {names.size} original DVR norm-residue declarations: \
    standard axioms only."
