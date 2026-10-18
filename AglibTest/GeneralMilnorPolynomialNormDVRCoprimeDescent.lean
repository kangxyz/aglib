/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRCoprimeDescent
import Lean.Util.CollectAxioms

/-! Direct all-class consumer of the actual finite coprime norm-residue square. -/

open Polynomial Polynomial.LocalResidue
open IsLocalRing
open MilnorK MilnorK.PolynomialResidue
open MilnorK.PolynomialNorm

namespace AglibTest.GeneralMilnorPolynomialNormDVRCoprimeDescent

variable {F L : Type*} [Field F] [Field L] [CharZero F] [CharZero L]
  [Algebra F L] [Module.Finite F L]
  (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R F] [IsFractionRing R F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Algebra S (AdjoinRoot p.val)] [IsFractionRing S (AdjoinRoot p.val)]
  (T : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra R T] [IsLocalHom (algebraMap R T)]
  [Algebra T L] [IsFractionRing T L] [Algebra R L]
  [IsScalarTower R F L] [IsScalarTower R T L]
  (pL : MonicIrreducible L) (hpL : pL.val = p.val.map (algebraMap F L))
  (U : Type*) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
  [HenselianLocalRing U] [Algebra S U] [Algebra T U] [Algebra R U]
  [IsLocalHom (algebraMap S U)] [IsLocalHom (algebraMap T U)]
  [IsLocalHom (algebraMap R U)]
  [IsScalarTower R S U] [IsScalarTower R T U]
  [Algebra U (AdjoinRoot pL.val)] [IsFractionRing U (AdjoinRoot pL.val)]
  [IsScalarTower T U (AdjoinRoot pL.val)] [IsIntegralClosure U T (AdjoinRoot pL.val)]
  [Module.Finite T U] [Module.IsTorsionFree T U]
  [CharZero (ResidueField R)] [CharZero (ResidueField T)]
  [Module.Finite R T]

variable [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsScalarTower R S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]
  [Normal F (AdjoinRoot p.val)]
  [Module.IsTorsionFree R T] [IsIntegralClosure T R L]
  [Module.Finite S U] [Module.IsTorsionFree S U]
  [Algebra (AdjoinRoot p.val) (AdjoinRoot pL.val)]
  [Algebra S (AdjoinRoot pL.val)]
  [IsScalarTower S (AdjoinRoot p.val) (AdjoinRoot pL.val)]
  [IsScalarTower S U (AdjoinRoot pL.val)]
  [IsScalarTower F (AdjoinRoot p.val) (AdjoinRoot pL.val)]
  [IsIntegralClosure U S (AdjoinRoot pL.val)]


/-- The actual all-class residue equality, with every finite diagram hypothesis visible. -/
theorem actual_coprime_norm_residue_square
    (hscalar : algebraMap (AdjoinRoot p.val) (AdjoinRoot pL.val) = scalarRootMap p pL hpL)
    (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1))
    (hx : map (n + 1) (scalarRootMap p pL hpL) x ∈
      mixedSpan (algebraMap L (AdjoinRoot pL.val)) n)
    {π : R} {ϖ : S} {τ : T} {υ : U}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (hτ : Irreducible τ) (hυ : Irreducible υ)
    (u : Sˣ) (v : Tˣ) (w z : Uˣ) (e a b c : ℕ)
    (hRS : algebraMap R S π = (u : S) * ϖ ^ e)
    (hRT : algebraMap R T π = (v : T) * τ ^ a)
    (hSU : algebraMap S U ϖ = (w : U) * υ ^ b)
    (hTU : algebraMap T U τ = (z : U) * υ ^ c)
    (hcunit : IsUnit (c : U)) (hp : p.val.natDegree.Prime)
    (hcop : p.val.natDegree.Coprime (Module.finrank F L))
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S) :
    DVR.residue R F n (polynomialNorm (n + 1) p x) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n x)) :=
  residue_polynomialNorm_of_coprime_mixed_diagram R p S T pL hpL U hscalar
    n x hx hπ hϖ hτ hυ u v w z e a b c hRS hRT hSU hTU hcunit hp hcop q ε

end AglibTest.GeneralMilnorPolynomialNormDVRCoprimeDescent

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.CoprimeIrreducibility,
    `Aglib.FieldTheory.FiniteCoprimeSplitting,
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.FieldTheory.SylowFixedField,
    `Aglib.RingTheory.AdjoinRootCoefficientEquiv,
    `Aglib.RingTheory.AdjoinRootScalarBranches,
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
    `AglibTest.GeneralMilnorPolynomialNormDVRCoprimeDescent]
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
  logInfo m!"Checked {names.size} coprime descent and Milnor declarations: \
    standard axioms only."
