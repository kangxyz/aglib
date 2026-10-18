/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.FiniteExtension.WeightedBranches
import Aglib.KTheory.MilnorK.Norm.FiniteExtension.DVRRestrictionKernel
import Aglib.KTheory.MilnorK.Norm.FiniteExtension.CompleteRamifiedBranch
import Aglib.KTheory.MilnorK.Norm.Polynomial.CompleteBranchSum
import Aglib.RingTheory.AdjoinRootTensorBranchProduct
import Lean.Util.CollectAxioms

/-! Literal weighted residue-branch norm refinement consumer. -/

namespace AglibTest.GeneralMilnorWeightedNormBranches

open MilnorK IsLocalRing Polynomial PolynomialResidue PolynomialNorm
  Polynomial.LocalResidue AdjoinRoot

attribute [local instance] MilnorK.rootFinite

universe u v

/-- Refining each residue scalar branch by finite fields preserves the norm
sum with the exact degree-weighted multiplicity. -/
theorem actual_weighted_branch_square
    {k L : Type u} [Field k] [CharZero k] [Field L] [CharZero L] [Algebra k L]
    (p : MonicIrreducible k)
    [Fintype (IrreducibleBranch (p.val.map (algebraMap k L)))]
    (I : IrreducibleBranch (p.val.map (algebraMap k L)) → Type v) [∀ j, Fintype (I j)]
    (D : (j : IrreducibleBranch (p.val.map (algebraMap k L))) → I j → Type u)
    [∀ j i, Field (D j i)] [∀ j i, Algebra L (D j i)]
    [∀ j i, Algebra (AdjoinRoot j.val.val) (D j i)]
    [∀ j i, IsScalarTower L (AdjoinRoot j.val.val) (D j i)]
    [∀ j i, FiniteDimensional L (D j i)]
    [∀ j i, FiniteDimensional (AdjoinRoot j.val.val) (D j i)]
    (b : (j : IrreducibleBranch (p.val.map (algebraMap k L))) → I j → ℕ)
    (a : ℕ)
    (hcount : ∀ j, ∑ i, b j i * Module.finrank (AdjoinRoot j.val.val) (D j i) = a)
    (n : ℕ) (x : K (AdjoinRoot p.val) n) :
    a • map n (algebraMap k L) (polynomialNorm n p x) =
      ∑ j, ∑ i, b j i • finiteExtensionNorm L (D j i) n
        (map n ((algebraMap (AdjoinRoot j.val.val) (D j i)).comp
          (adjoinRootMap (algebraMap k L) p.val j.val.val j.property)) x) :=
  polynomialNorm_restrict_weighted_branches p I D b a hcount n x

/-- A ramification-weighted residue restriction is detected up to the actual
fraction-field extension degree, not merely the residue degree. -/
theorem actual_degree_annihilator
    (R S F E : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsLocalHom (algebraMap R S)] [CharZero (ResidueField R)]
    [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E] [FiniteDimensional F E]
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (n : ℕ) (z : K (ResidueField R) n)
    (hz : e • map n (algebraMap (ResidueField R) (ResidueField S)) z = 0) :
    Module.finrank F E • z = 0 :=
  degree_smul_eq_zero_of_ramified_residue_restrict R S F E hπ hϖ u e he n z hz

/-- Each actual upper p-group branch contributes its literal ramification weight. -/
theorem actual_ramified_upper_square
    (S T U E L D Ω : Type u)
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [IsAdicComplete (maximalIdeal T) T] [CharZero (ResidueField T)]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Field L] [CharZero L] [Algebra T L] [IsFractionRing T L]
    [Field D] [CharZero D] [Algebra L D] [FiniteDimensional L D]
    [Algebra T D] [IsScalarTower T L D]
    [Algebra T U] [Module.Finite T U] [IsLocalHom (algebraMap T U)]
    [Algebra U D] [IsScalarTower T U D] [IsFractionRing U D]
    [IsIntegralClosure U T D]
    [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω)) (g : D →ₐ[L] Ω)
    (j : S →+* U) [IsLocalHom j] (f : E →+* D)
    (hf : ∀ s, f (algebraMap S E s) = algebraMap U D (j s))
    {ϖ : S} {ρ : U} (hϖ : Irreducible ϖ) (hρ : Irreducible ρ)
    (w : Uˣ) (b : ℕ) (hb : j ϖ = (w : U) * ρ ^ b)
    (n : ℕ) (x : K E (n + 1)) :
    DVR.residue T L n (finiteExtensionNorm L D (n + 1) (map (n + 1) f x)) =
      b • finiteExtensionNorm (ResidueField T) (ResidueField U) n
        (map n (ResidueField.map j) (DVR.residue S E n x)) :=
  residue_norm_restrict_complete_pGroup_branch S T U E L D Ω ℓ hG g
    j f hf hϖ hρ w b hb n x

/-- The restricted residue of the original norm is the full upper branch sum,
with each original vertical ramification exponent visible. -/
theorem actual_full_ramified_branch_sum
    {F L : Type u} [Field F] [CharZero F] [Field L] [CharZero L] [Algebra F L]
    (R S T : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R F] [IsFractionRing R F]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [IsAdicComplete (maximalIdeal T) T] [CharZero (ResidueField T)]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    [Algebra T L] [IsFractionRing T L] [Algebra R L]
    [IsScalarTower R F L] [IsScalarTower R T L]
    (p : MonicIrreducible F)
    [Algebra S (AdjoinRoot p.val)] [IsFractionRing S (AdjoinRoot p.val)]
    [Fintype (IrreducibleBranch (p.val.map (algebraMap F L)))]
    (U : IrreducibleBranch (p.val.map (algebraMap F L)) → Type u)
    [∀ r, CommRing (U r)] [∀ r, IsDomain (U r)] [∀ r, IsDiscreteValuationRing (U r)]
    [∀ r, Algebra T (U r)] [∀ r, Module.Finite T (U r)]
    [∀ r, IsLocalHom (algebraMap T (U r))]
    [∀ r, Algebra (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsScalarTower T (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsFractionRing (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsIntegralClosure (U r) T (AdjoinRoot r.val.val)]
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : ∀ r : IrreducibleBranch (p.val.map (algebraMap F L)),
      AdjoinRoot r.val.val →ₐ[L] Ω)
    (j : ∀ r, S →+* U r) [∀ r, IsLocalHom (j r)]
    (hj : ∀ r s, adjoinRootMap (algebraMap F L) p.val r.val.val r.property
      (algebraMap S (AdjoinRoot p.val) s) =
        algebraMap (U r) (AdjoinRoot r.val.val) (j r s))
    {π : R} {ϖ : S} {τ : T}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (hτ : Irreducible τ)
    (ρ : ∀ r, U r) (hρ : ∀ r, Irreducible (ρ r))
    (v : Tˣ) (a : ℕ) (ha : algebraMap R T π = (v : T) * τ ^ a)
    (w : ∀ r, (U r)ˣ) (b : IrreducibleBranch (p.val.map (algebraMap F L)) → ℕ)
    (hb : ∀ r, j r ϖ = (w r : U r) * ρ r ^ b r)
    (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    a • map n (ResidueField.map (algebraMap R T))
      (DVR.residue R F n (polynomialNorm (n + 1) p x)) =
      ∑ r, b r • finiteExtensionNorm (ResidueField T) (ResidueField (U r)) n
        (map n (ResidueField.map (j r)) (DVR.residue S (AdjoinRoot p.val) n x)) :=
  ramification_restrict_residue_polynomialNorm_eq_branch_sum R S T p U Ω ℓ hG g
    j hj hπ hϖ hτ ρ hρ v a ha w b hb n x

end AglibTest.GeneralMilnorWeightedNormBranches

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
    `Aglib.RingTheory.AdjoinRootNestedBranches,
    `Aglib.RingTheory.AdjoinRootPiBranches,
    `Aglib.RingTheory.AdjoinRootScalarBranches,
    `Aglib.RingTheory.AdjoinRootTensorBranchProduct,
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
    `Aglib.RingTheory.IntermediateIntegralClosureTower,
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
    `AglibTest.GeneralMilnorWeightedNormBranches]
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
  logInfo m!"Checked {names.size} weighted scalar branch and Milnor declarations: \
    standard axioms only."
