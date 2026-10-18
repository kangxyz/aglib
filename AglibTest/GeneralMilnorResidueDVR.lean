/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.DVR
import Lean.Util.CollectAxioms

/-! Consumers of canonical all-degree residues of actual DVRs. They use the
literal fraction-field units and original residue ring map; degree-two and
three comparisons retain the existing low-degree maps on all quotient classes. -/

open MilnorK

namespace AglibTest.GeneralMilnorResidueDVR

variable (R L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- The actual all-degree map requires only a DVR and its fraction field. -/
noncomputable def actual_residue (n : ℕ) :
    K L (n + 1) →ₗ[ℤ] K (IsLocalRing.ResidueField R) n := DVR.residue R L n

/-- Uniformizer independence is proved for every actual quotient class. -/
theorem independent_uniformizer {π π' : R} (hπ : Irreducible π) (hπ' : Irreducible π')
    (n : ℕ) : DVR.residueWithUniformizer R L hπ' n = DVR.residueWithUniformizer R L hπ n :=
  DVR.residueWithUniformizer_independent R L hπ hπ' n

/-- Embedded ring-unit symbols have zero canonical residue. -/
theorem ring_units (n : ℕ) (a : Fin (n + 1) → Rˣ) :
    DVR.residue R L n (symbol (MilnorK.K2.DVR.fieldUnits R L ∘ a)) = 0 :=
  DVR.residue_ring_units R L n a

/-- Last-slot uniformizer normalization is literal coordinatewise ring reduction. -/
theorem uniformizer_normalization {π : R} (hπ : Irreducible π) (n : ℕ) (a : Fin n → Rˣ) :
    DVR.residue R L n (symbol (Fin.snoc (MilnorK.K2.DVR.fieldUnits R L ∘ a)
      (MilnorK.K2.DVR.uniformizer (K := L) hπ))) =
      symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) :=
  DVR.residue_ring_units_uniformizer R L hπ n a

/-- Degree-one normalization includes the empty prefix, rather than starting at K₂. -/
theorem uniformizer_value_one {π : R} (hπ : Irreducible π) :
    zeroEquiv (IsLocalRing.ResidueField R)
      (DVR.residue R L 0 (symbol ![MilnorK.K2.DVR.uniformizer (K := L) hπ])) = 1 := by
  rw [DVR.zeroEquiv_residue]
  simp only [oneEquiv_symbol]
  exact MilnorK.K2.DVR.value_uniformizer hπ

/-- Principal-unit vanishing allows arbitrary other fraction-field entries. -/
theorem arbitrary_other_poles (n : ℕ) (a : SymbolTuple L (n + 1)) (i : Fin (n + 1))
    (u : Rˣ) (hi : a i = MilnorK.K2.DVR.fieldUnits R L u)
    (hu : Units.map (IsLocalRing.residue R).toMonoidHom u = 1) :
    DVR.residue R L n (symbol a) = 0 := DVR.residue_principal_ring_unit R L n a i u hi hu

/-- A principal ring unit kills an actual degree-four symbol containing two explicit poles. -/
theorem explicit_poles {π : R} (hπ : Irreducible π) (u : Rˣ)
    (hu : Units.map (IsLocalRing.residue R).toMonoidHom u = 1) :
    DVR.residue R L 3 (symbol ![MilnorK.K2.DVR.uniformizer (K := L) hπ ^ (-1 : ℤ),
      MilnorK.K2.DVR.fieldUnits R L u, MilnorK.K2.DVR.uniformizer (K := L) hπ ^ (-3 : ℤ),
      MilnorK.K2.DVR.uniformizer (K := L) hπ]) = 0 :=
  DVR.residue_principal_ring_unit R L 3 _ 1 u rfl hu

/-- Repeated actual uniformizers keep every target minus-one entry. -/
theorem repeated_uniformizers {π : R} (hπ : Irreducible π) (n : ℕ) :
    DVR.residue R L n (symbol (fun _ => MilnorK.K2.DVR.uniformizer (K := L) hπ)) =
      symbol (fun _ => (-1 : (IsLocalRing.ResidueField R)ˣ)) :=
  DVR.residue_uniformizers R L hπ n

/-- The existing tame normalization is preserved on all actual degree-two classes. -/
theorem old_tame (x : K L 2) :
    oneEquiv (IsLocalRing.ResidueField R) (DVR.residue R L 1 x) =
      MilnorK.K2.tame (MilnorK.K2.DVR.chosenData R L) (twoEquiv L x) :=
  DVR.oneEquiv_residue_one R L x

/-- The existing canonical degree-three DVR residue is preserved on every class. -/
theorem old_residue_three (x : K L 3) :
    twoEquiv (IsLocalRing.ResidueField R) (DVR.residue R L 2 x) =
      MilnorK.K3.DVR.residue R L (threeEquiv L x) := DVR.twoEquiv_residue_two R L x

end AglibTest.GeneralMilnorResidueDVR

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
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorResidueDVR]
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
  logInfo m!"Checked {names.size} actual DVR residue and general Milnor declarations: \
    standard axioms only."
