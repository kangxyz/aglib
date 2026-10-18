/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRRingUnit
import Aglib.RingTheory.CompleteDVRExtension
import Lean.Util.CollectAxioms

/-! Direct consumers of the genuinely ramified final-ring-unit norm square.
The prefix is an arbitrary quotient class; it need not have unit coordinates.
The complete-DVR consumer constructs all source local data and ramification. -/

open Polynomial Polynomial.LocalResidue IsLocalRing
open MilnorK MilnorK.PolynomialResidue MilnorK.PolynomialNorm

namespace AglibTest.GeneralMilnorPolynomialNormDVRRingUnit

section ActualExtension

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)] [CharZero (ResidueField R)]
  [Algebra S (AdjoinRoot p.val)] [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
  (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
  (q : MonicIrreducible (ResidueField R))
  (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S)

include hπ hϖ he

/-- All original prefix classes, not only symbols with integral coordinates. -/
theorem arbitrary_prefix (n : ℕ) (x : K F n) (b : Sˣ) :
    DVR.residue R F n (polynomialNorm (n + 1) p
      (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x)
        (Additive.ofMul (MilnorK.K2.DVR.fieldUnits S (AdjoinRoot p.val) b)))) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n
          (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x)
            (Additive.ofMul (MilnorK.K2.DVR.fieldUnits S (AdjoinRoot p.val) b))))) :=
  residue_polynomialNorm_final_ring_unit R F p S n x b hπ hϖ u e he q ε

/-- A prefix consisting entirely of repeated source poles is explicitly included. -/
theorem repeated_uniformizer_poles (n : ℕ) (b : Sˣ) :
    DVR.residue R F n (polynomialNorm (n + 1) p (productUnit n
      (map n (algebraMap F (AdjoinRoot p.val))
        (symbol (fun _ => MilnorK.K2.DVR.uniformizer (K := F) hπ ^ (-3 : ℤ))))
      (Additive.ofMul (MilnorK.K2.DVR.fieldUnits S (AdjoinRoot p.val) b)))) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n (productUnit n
          (map n (algebraMap F (AdjoinRoot p.val))
            (symbol (fun _ => MilnorK.K2.DVR.uniformizer (K := F) hπ ^ (-3 : ℤ))))
          (Additive.ofMul (MilnorK.K2.DVR.fieldUnits S (AdjoinRoot p.val) b))))) :=
  arbitrary_prefix R F p S hπ hϖ u e he q ε n _ b

/-- The literal empty prefix is included rather than excluded by positive-degree induction. -/
theorem empty_prefix (x : K F 0) (b : Sˣ) :
    DVR.residue R F 0 (polynomialNorm 1 p (productUnit 0
      (map 0 (algebraMap F (AdjoinRoot p.val)) x)
      (Additive.ofMul (MilnorK.K2.DVR.fieldUnits S (AdjoinRoot p.val) b)))) =
      polynomialNorm 0 q (map 0 ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) 0 (productUnit 0
          (map 0 (algebraMap F (AdjoinRoot p.val)) x)
          (Additive.ofMul (MilnorK.K2.DVR.fieldUnits S (AdjoinRoot p.val) b))))) :=
  arbitrary_prefix R F p S hπ hϖ u e he q ε 0 x b

end ActualExtension

section Complete

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]
  [Field F] [Algebra R F] [IsFractionRing R F] [CharZero (ResidueField R)]

/-- The source is the actual integral closure, and its uniformizer equation is
constructed from completeness and the finite separable root extension. -/
theorem complete_DVR_arbitrary_prefix (p : MonicIrreducible F) :
    let _ : CharZero R := RingHom.charZero (residue R)
    let _ : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
    let _ := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
    let _ := IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing
      R F (AdjoinRoot p.val)
    let _ := IsDiscreteValuationRing.CompleteExtension.integralClosure_isLocalHom R F (AdjoinRoot p.val)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension
      R F (AdjoinRoot p.val) (integralClosure R (AdjoinRoot p.val))
    ∀ (n : ℕ) (x : K F n) (b : (integralClosure R (AdjoinRoot p.val))ˣ)
      (q : MonicIrreducible (ResidueField R))
      (ε : AdjoinRoot q.val ≃ₐ[ResidueField R]
        ResidueField (integralClosure R (AdjoinRoot p.val))),
    DVR.residue R F n (polynomialNorm (n + 1) p (productUnit n
      (map n (algebraMap F (AdjoinRoot p.val)) x)
      (Additive.ofMul (MilnorK.K2.DVR.fieldUnits (integralClosure R (AdjoinRoot p.val))
        (AdjoinRoot p.val) b)))) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) n (productUnit n
          (map n (algebraMap F (AdjoinRoot p.val)) x)
          (Additive.ofMul (MilnorK.K2.DVR.fieldUnits (integralClosure R (AdjoinRoot p.val))
            (AdjoinRoot p.val) b))))) := by
  let : CharZero R := RingHom.charZero (residue R)
  let : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let : FiniteDimensional F (AdjoinRoot p.val) :=
    (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
  let S := integralClosure R (AdjoinRoot p.val)
  let : IsDiscreteValuationRing S :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing R F (AdjoinRoot p.val)
  let : IsLocalHom (algebraMap R S) :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_isLocalHom R F (AdjoinRoot p.val)
  let : IsFractionRing S (AdjoinRoot p.val) :=
    IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot p.val) S
  let : Module.Finite R S := IsIntegralClosure.finite R F (AdjoinRoot p.val) S
  let : Module.IsTorsionFree R S := (Module.isTorsionFree_iff_algebraMap_injective).mpr
    (IsDiscreteValuationRing.CompleteExtension.integralClosure_algebraMap_injective R F (AdjoinRoot p.val))
  dsimp only
  intro n x b q ε
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨e, _, u, he⟩ :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_exists_positive_ramification
      R F (AdjoinRoot p.val) hπ hϖ
  exact residue_polynomialNorm_final_ring_unit R F p S n x b hπ hϖ u e he q ε

end Complete

end AglibTest.GeneralMilnorPolynomialNormDVRRingUnit

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.RingTheory.AdjoinRootScalarBranches,
    `Aglib.RingTheory.CompleteDVRExtension,
    `Aglib.RingTheory.DVRNormResidueUnit,
    `Aglib.RingTheory.DVRNormValuation,
    `Aglib.RingTheory.FiniteAlgebraNormLength,
    `Aglib.RingTheory.FiniteLength.FiniteAlgebraFiber,
    `Aglib.RingTheory.FiniteLength.FiniteAlgebraLength,
    `Aglib.RingTheory.FiniteLength.Support,
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
    `AglibTest.GeneralMilnorPolynomialNormDVRRingUnit]
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
  logInfo m!"Checked {names.size} ramified final-unit and general Milnor declarations: \
    standard axioms only."
