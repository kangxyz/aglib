/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.FiniteExtension.ProductBaseChange
import Lean.Util.CollectAxioms

/-! Actual field tensor coordinate maps, with no norm law assumption. -/

namespace AglibTest.GeneralMilnorNormProductBaseChange

open MilnorK
open scoped TensorProduct

variable {k L ι : Type*} [Field k] [CharZero k] [Field L] [CharZero L]
  [Algebra k L] [Fintype ι]
  (D : ι → Type*) [∀ i, Field (D i)] [∀ i, Algebra L (D i)]
  [∀ i, FiniteDimensional L (D i)]

/-- Direct consumer keeps the actual tensor-coordinate restriction map. -/
theorem actual_tensor_coordinate_norms
    (E : Type*) [Field E] [Algebra k E] [FiniteDimensional k E]
    (e : L ⊗[k] E ≃ₐ[L] ∀ i, D i) (n : ℕ) (x : K E n) :
    map n (algebraMap k L) (finiteExtensionNorm k E n x) =
      ∑ i, finiteExtensionNorm L (D i) n
        (map n (((Pi.evalRingHom D i).comp e.toRingHom).comp
          Algebra.TensorProduct.includeRight.toRingHom) x) :=
  finiteExtensionNorm_restrict_tensorProduct D E e n x

end AglibTest.GeneralMilnorNormProductBaseChange

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
    `Aglib.RingTheory.AdjoinRootFieldProductBranches,
    `Aglib.RingTheory.AdjoinRootPiBranches,
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
    `AglibTest.GeneralMilnorNormProductBaseChange]
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
  logInfo m!"Checked {names.size} actual tensor-coordinate norm declarations: \
    standard axioms only."
