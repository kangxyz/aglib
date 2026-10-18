/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Dedekind.AffineNormSpecialization
import Lean.Util.CollectAxioms

/-! Direct consumers of actual arbitrary linear-place specialization, including
degree zero and original affine norm endpoint equality with no boundary premise. -/

namespace AglibTest.GeneralMilnorAffineNormSpecialization

open MilnorK Polynomial
open PolynomialResidue DedekindResidue

section Constants

variable {k : Type*} [Field k]

local instance (a : k) : Fact (Irreducible (X - C a)) :=
  ⟨irreducible_X_sub_C a⟩

/-- Literal DVR specialization, followed by actual residue-field evaluation,
recovers an arbitrary original quotient class at every point. -/
theorem literal_linear_specialization (a : k) (n : ℕ) (x : K k n) :
    map n (linearRootEquiv a).toRingHom
      (specializeAt (X - C a) n (map n (RatFunc.C : k →+* RatFunc k) x)) = x :=
  linearSpecialization_constants a n x

/-- Recovery in degree zero includes every integer, not just the empty symbol. -/
theorem degree_zero_integer (a : k) (z : ℤ) :
    zeroEquiv k (linearSpecialization a 0
      (map 0 (RatFunc.C : k →+* RatFunc k) ((zeroEquiv k).symm z))) = z := by
  rw [linearSpecialization_constants, LinearEquiv.apply_symm_apply]

/-- The actual evaluated residue of a last-slot linear uniformizer recovers
an arbitrary constant quotient class in every degree. -/
theorem literal_linear_residue (a : k) (n : ℕ) (x : K k n) :
    map n (linearRootEquiv a).toRingHom
      (residueAt (X - C a) n
        (productUnit n (map n (RatFunc.C : k →+* RatFunc k) x)
          (Additive.ofMul (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero)))) = x :=
  linearResidue_productUnit_constants a n x

/-- Arbitrary constant-image classes have equal specializations at zero and one. -/
theorem zero_one_constant_image (n : ℕ) (x : K (RatFunc k) n)
    (hx : x ∈ LinearMap.range (map n (RatFunc.C : k →+* RatFunc k))) :
    linearSpecialization (0 : k) n x = linearSpecialization (1 : k) n x :=
  linearSpecialization_eq_of_mem_constant_range 0 1 n x hx

end Constants

section AffineNorm

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

/-- The norm of any everywhere unramified class has equal endpoint values. -/
theorem all_class_norm_endpoints (a b : k) (n : ℕ) (x : K E (n + 1))
    (hx : totalResidue S E n x = 0) :
    linearSpecialization a (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1) x) =
      linearSpecialization b (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1) x) :=
  linearSpecialization_norm_eq_of_totalResidue_zero k S E a b n x hx

/-- Endpoint equality for the actual norm of original global-unit symbols
requires neither a supplied zero-residue premise nor a supplied boundary. -/
theorem actual_global_unit_norm_zero_one (n : ℕ) (u : Fin (n + 1) → Sˣ) :
    linearSpecialization (0 : k) (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
      (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) =
      linearSpecialization (1 : k) (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
        (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) :=
  linearSpecialization_norm_ring_unit_symbol_eq k S E 0 1 n u

/-- The two endpoint residues of the actual normalized norm, each with its own
literal last-slot linear uniformizer, agree without assuming a boundary. -/
theorem actual_norm_last_slot_endpoint_residues (a b : k) (n : ℕ)
    (u : Fin (n + 1) → Sˣ) :
    linearResidue a (n + 1)
      (productUnit (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
        (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u)))
        (Additive.ofMul (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero))) =
      linearResidue b (n + 1)
        (productUnit (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
          (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u)))
          (Additive.ofMul (polynomialUnit (X - C b) (irreducible_X_sub_C b).ne_zero))) := by
  rw [linearResidue_norm_ring_unit_symbol_productUnit k S E,
    linearResidue_norm_ring_unit_symbol_productUnit k S E]
  exact linearSpecialization_norm_ring_unit_symbol_eq k S E a b n u

end AffineNorm
end AglibTest.GeneralMilnorAffineNormSpecialization

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
  let prefixes := #[`MilnorK,
    `AglibTest.GeneralMilnorAffineNormSpecialization]
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
  logInfo m!"Checked {names.size} affine norm specialization and Milnor declarations: \
    standard axioms only."
