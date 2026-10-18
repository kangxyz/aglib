/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Aglib.KTheory.MilnorK.Dedekind.NormalizedCurveReciprocity
import Lean.Util.CollectAxioms

/-! # Reciprocity on the original finite model and every original infinity branch -/

noncomputable section

namespace AglibTest.GeneralMilnorCurveReciprocity
open MilnorK MilnorK.DedekindResidue

open Polynomial IsLocalRing IsDedekindDomain

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S] [Algebra k S] [IsScalarTower k k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

open scoped Classical in
/-- Reciprocity for a finite Dedekind model of the affine line, including every
branch of its original function field above infinity. -/
theorem actual_original_curve_sum (n : ℕ) (x : K E (n + 1)) :
    letI : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
      (inferInstanceAs (Algebra.FiniteType k k[X]))
      (inferInstanceAs (Algebra.FiniteType k[X] S))
    letI : ∀ q : HeightOneSpectrum S,
        FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
      fun q => Localization.finiteType_localResidue_finite k S q.asIdeal
    (∑ q ∈ (totalResidue S E n x).support,
      finiteExtensionNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n
        (DVR.residue (Localization.AtPrime q.asIdeal) E n x)) +
      infinityBranchResidueSum k E n x = 0 := by
  let : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
    (inferInstanceAs (Algebra.FiniteType k k[X]))
    (inferInstanceAs (Algebra.FiniteType k[X] S))
  let : ∀ q : HeightOneSpectrum S,
      FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
    fun q => Localization.finiteType_localResidue_finite k S q.asIdeal
  rw [← normedTotalResidue_eq_sum]
  exact normalized_curve_reciprocity k S E n x

end AglibTest.GeneralMilnorCurveReciprocity

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
    `Aglib.RingTheory.FiniteLocalResidue,
    `Aglib.RingTheory.FiniteTypeLocalResidue,
    `Aglib.RingTheory.HenselianPrincipalRoots,
    `Aglib.RingTheory.HenselianUniformizerNormalization,
    `Aglib.RingTheory.IntegralTensorCharpolyProduct,
    `Aglib.RingTheory.IntermediateIntegralClosureTower,
    `Aglib.RingTheory.Length.ExactSequence,
    `Aglib.RingTheory.LocalizedDedekindBranches,
    `Aglib.RingTheory.LocalizedDedekindFractions,
    `Aglib.RingTheory.LocalizedPrimeBranches,
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
    `AglibTest.GeneralMilnorCurveReciprocity]
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
  logInfo m!"Checked {names.size} original curve reciprocity declarations: \
    standard axioms only."
