/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Specialization
import Lean.Util.CollectAxioms

/-! Direct consumers for all-degree specialization, arbitrary unit-part twists,
negative valuation behavior, degree zero and the literal actual-DVR adapter. -/

open MilnorK

namespace AglibTest.GeneralMilnorResidueSpecialization

universe u v

variable {L : Type u} {κ : Type v} [Field L] [Field κ]
variable (d : MilnorK.K2.DiscreteResidueData L κ) (hd : MilnorK.K2.UnitReductionCompatible d)

/-- A residue-unit twist preserves the actual symbol quotient in every degree. -/
theorem arbitrary_twist (e : Additive κˣ) (n : ℕ) (a : SymbolTuple L n) :
    specializeTwist d hd e n (symbol a) = symbol (unitPartTwistMul d e ∘ a) :=
  specializeTwist_symbol d hd e n a

/-- Negative valuation pairs retain their minus-one discrepancy after every twist. -/
theorem negative_pair (e : Additive κˣ) (a b : Lˣ)
    (hab : (a : L) + (b : L) = 1) (ha : d.value (Additive.ofMul a) < 0) :
    unitPartTwist d e (Additive.ofMul b) =
      unitPartTwist d e (Additive.ofMul a) + MilnorK.K2.residueSign κ := by
  obtain ⟨hv, hu⟩ := d.negative a b hab ha
  simp only [unitPartTwist_apply, hv, hu]
  abel

/-- The degree-zero construction acts identically on the canonical integers. -/
theorem degree_zero (e : Additive κˣ) (x : K L 0) :
    zeroEquiv κ (specializeTwist d hd e 0 x) = zeroEquiv L x := by
  have h : (zeroEquiv κ).toLinearMap.comp (specializeTwist d hd e 0) =
      (zeroEquiv L).toLinearMap := by
    apply linearMap_ext
    intro a
    simp
  exact LinearMap.congr_fun h x

/-- Degree one is exactly the original normalized residue-unit-part homomorphism. -/
theorem degree_one (a : Lˣ) :
    oneEquiv κ (specialize d hd 1 (symbol ![a])) = d.unitPart (Additive.ofMul a) := by
  simp

/-- Arbitrary twists can give a nonzero specialization of the uniformizer. -/
theorem twisted_uniformizer (e : Additive κˣ) :
    oneEquiv κ (specializeTwist d hd e 1 (symbol ![d.uniformizer])) = -e := by
  simp [d.unitPart_uniformizer, d.value_uniformizer]

/-- The old degree-two specialization is compared on every class, not only normalized ones. -/
theorem old_specialization (x : K L 2) :
    twoEquiv κ (specialize d hd 2 x) = MilnorK.K2.specialize d hd (twoEquiv L x) :=
  twoEquiv_specialize d hd x

variable (R M : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field M] [Algebra R M] [IsFractionRing R M]

/-- The general-degree adapter uses the actual DVR residue ring homomorphism. -/
theorem actual_DVR_reduction {π : R} (hπ : Irreducible π) (n : ℕ) (a : Fin n → Rˣ) :
    DVR.specializeWithUniformizer R M hπ n
      (symbol (MilnorK.K2.DVR.fieldUnits R M ∘ a)) =
      symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) :=
  DVR.specializeWithUniformizer_ring_units R M hπ n a

end AglibTest.GeneralMilnorResidueSpecialization

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName)
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorResidueSpecialization]
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
  logInfo m!"Checked {names.size} specialization and general Milnor declarations: \
    standard axioms only."
