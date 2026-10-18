/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.FiniteExtension.RationalResidue
import Lean.Util.CollectAxioms

/-! Direct consumers of the general finite-place norm square on the actual
fields, with the entire original residue-field branch sum displayed. -/

open Polynomial Polynomial.LocalResidue AdjoinRoot
open MilnorK PolynomialResidue
open scoped RatFunc

attribute [local instance] Polynomial.algebra AdjoinRoot.scalarBranchAlgebra
  MilnorK.residueRootFinite MilnorK.residueRootCharZero MilnorK.primeRationalFinite

namespace AglibTest.GeneralMilnorFiniteExtensionNormRationalResidue

universe u

/-- Every finite coefficient field, finite place, Milnor degree, and original
quotient class is admitted, without normality or a supplied residue square. -/
theorem actual_arbitrary_finite_square
    {k : Type u} [Field k] [CharZero k] (E : Type u) [Field E]
    [Algebra k E] [FiniteDimensional k E] (h : MonicIrreducible k)
    (n : ℕ) (x : K (RatFunc E) (n + 1)) :
    residueAt h.val n (finiteExtensionNorm (RatFunc k) (RatFunc E) (n + 1) x) =
      rationalResidueNormSum k E h n x :=
  residueAt_finiteExtensionNorm_rational E h n x

open scoped Classical in
/-- Expanded complete branch formula: each summand is the actual finite norm
of the original residue-field extension, with its literal coefficient action. -/
theorem original_full_residue_norm_sum
    {k : Type u} [Field k] [CharZero k] (E : Type u) [Field E]
    [Algebra k E] [FiniteDimensional k E] (h : MonicIrreducible k)
    (n : ℕ) (x : K (RatFunc E) (n + 1)) :
    letI : Finite (IrreducibleBranch (h.val.map (algebraMap k E))) :=
      finite_irreducibleBranch _ (h.property.1.map _)
    letI : Fintype (IrreducibleBranch (h.val.map (algebraMap k E))) := Fintype.ofFinite _
    residueAt h.val n (finiteExtensionNorm (RatFunc k) (RatFunc E) (n + 1) x) =
      ∑ r : IrreducibleBranch (h.val.map (algebraMap k E)),
        letI : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
          finiteDimensional_scalarBranch_residue h r
        finiteExtensionNorm (AdjoinRoot h.val) (AdjoinRoot r.val.val) n
          (residueAt r.val.val n x) :=
  residueAt_finiteExtensionNorm_rational E h n x

/-- The complete actual residue sum is independent of the coefficient-field
presentation by the explicitly proved literal coefficient transport. -/
theorem original_sum_coefficient_equivalence
    {k A B : Type u} [Field k] [CharZero k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] [FiniteDimensional k A] [FiniteDimensional k B]
    (φ : A ≃ₐ[k] B) (h : MonicIrreducible k) (n : ℕ)
    (x : K (RatFunc A) (n + 1)) :
    rationalResidueNormSum k B h n (map (n + 1) (fractionMap φ.toRingHom) x) =
      rationalResidueNormSum k A h n x :=
  rationalResidueNormSum_map_algEquiv φ h n x

end AglibTest.GeneralMilnorFiniteExtensionNormRationalResidue

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
    `Aglib.FieldTheory.RatFuncCoefficientEquiv,
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.FieldTheory.RatFuncTranslation,
    `Aglib.FieldTheory.RationalCoefficientRoot,
    `Aglib.FieldTheory.SylowFixedField,
    `Aglib.RingTheory.AdjoinRootBranchProduct,
    `Aglib.RingTheory.AdjoinRootCoefficientEquiv,
    `Aglib.RingTheory.AdjoinRootCoefficientTowerBranches,
    `Aglib.RingTheory.AdjoinRootNestedBaseChange,
    `Aglib.RingTheory.AdjoinRootNestedBranches,
    `Aglib.RingTheory.AdjoinRootPiBranches,
    `Aglib.RingTheory.AdjoinRootScalarBranchCoefficientEquiv,
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
  let prefixes := #[`AdjoinRoot, `Polynomial.LocalResidue, `MilnorK,
    `AglibTest.GeneralMilnorFiniteExtensionNormRationalResidue]
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
  logInfo m!"Checked {names.size} actual finite rational residue norm declarations: \
    standard axioms only."
