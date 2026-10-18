/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.DVRNormResidueUnit
import Lean.Util.CollectAxioms

/-! Direct consumers of determinant norm reduction through the actual closed
fiber and its ramification length. No separability or characteristic-zero
assumption occurs in this native algebraic result. -/

open IsLocalRing

namespace AglibTest.DVRNormResidueUnit

section LocalAlgebra

variable (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R]
  [Algebra R S] [Module.Free R S] [Module.Finite R S]

/-- The determinant specializes to the literal quotient, including nilpotents. -/
theorem actual_closed_fiber (b : S) :
    let _ : Algebra (ResidueField R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    Algebra.norm (ResidueField R)
      (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b) =
        residue R (Algebra.norm R b) :=
  Algebra.norm_closedFiber R S b

/-- A finite local algebra retains its true closed-fiber self-length. -/
theorem literal_fiber_length [IsLocalRing S] [IsLocalHom (algebraMap R S)] (b : S) :
    residue R (Algebra.norm R b) =
      Algebra.norm (ResidueField R) (residue S b) ^
        (Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
          (S ⧸ (maximalIdeal R).map (algebraMap R S))).toNat :=
  Algebra.residue_norm_eq_norm_residue_pow_length R S b

end LocalAlgebra

section DVR

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
  (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)

include hπ hϖ he

/-- Length is identified with the exponent by the actual ideal equation. -/
theorem actual_ramification_length :
    Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (S ⧸ (maximalIdeal R).map (algebraMap R S)) = e :=
  IsDiscreteValuationRing.closedFiber_length_eq_ramification R S hπ hϖ u e he

variable [Module.Finite R S] [Module.IsTorsionFree R S] [IsLocalHom (algebraMap R S)]

/-- The ring statement includes every element, even elements reducing to zero. -/
theorem arbitrary_element (b : S) :
    residue R (Algebra.intNorm R S b) =
      Algebra.norm (ResidueField R) (residue S b) ^ e :=
  Algebra.residue_intNorm_eq_norm_residue_pow R S hπ hϖ u e he b

/-- Units use the original integral norm and original two residue maps. -/
theorem actual_units (b : Sˣ) :
    Units.map (residue R).toMonoidHom (Units.map (Algebra.intNorm R S) b) =
      Units.map (Algebra.norm (ResidueField R))
        (Units.map (residue S).toMonoidHom b) ^ e :=
  Algebra.residueUnits_intNorm_eq_norm_pow R S hπ hϖ u e he b

/-- The same unit formula is valid in residue characteristic two. -/
theorem residue_characteristic_two [CharP (ResidueField R) 2] (b : Sˣ) :
    Units.map (residue R).toMonoidHom (Units.map (Algebra.intNorm R S) b) =
      Units.map (Algebra.norm (ResidueField R))
        (Units.map (residue S).toMonoidHom b) ^ e :=
  Algebra.residueUnits_intNorm_eq_norm_pow R S hπ hϖ u e he b

/-- Principal residue-one units stay residue-one after the actual integral norm. -/
theorem principal_unit (b : Sˣ) (hb : Units.map (residue S).toMonoidHom b = 1) :
    Units.map (residue R).toMonoidHom (Units.map (Algebra.intNorm R S) b) = 1 := by
  rw [actual_units R S hπ hϖ u e he b, hb, map_one, one_pow]

end DVR

end AglibTest.DVRNormResidueUnit

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.RingTheory.DVRNormResidueUnit,
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
  let native := #[`Algebra.norm_closedFiber,
    `Algebra.residue_norm_eq_norm_residue_pow_length,
    `IsDiscreteValuationRing.map_maximalIdeal_eq_pow_of_uniformizer,
    `IsDiscreteValuationRing.closedFiber_length_eq_ramification,
    `Algebra.residue_intNorm_eq_norm_residue_pow,
    `Algebra.residueUnits_intNorm_eq_norm_pow]
  let selectedDeclaration (name : Name) := native.contains name ||
    (`AglibTest.DVRNormResidueUnit).isPrefixOf name
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for name in native do names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} native DVR norm reduction declarations: standard axioms only."
