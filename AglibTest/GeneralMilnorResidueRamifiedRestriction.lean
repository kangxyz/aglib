/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.RamifiedRestriction
import Lean.Util.CollectAxioms

/-! Direct consumers of ramified restriction in every Milnor degree. The real
local map, fraction-field square, and literal uniformizer equation remain
explicit. Repeated uniformizers test the signed recursion and its parity term. -/

open MilnorK

namespace AglibTest.GeneralMilnorResidueRamifiedRestriction

variable {R S L M : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra R L] [IsFractionRing R L]
  [Field M] [Algebra S M] [IsFractionRing S M]
  (j : R →+* S) [IsLocalHom j] (f : L →+* M)
  (hf : ∀ r : R, f (algebraMap R L r) = algebraMap S M (j r))
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
  (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ϖ ^ e)

include hf hπ hϖ hπmap

/-- Arbitrary quotient classes, including symbols with poles, satisfy the square. -/
theorem arbitrary_class (n : ℕ) (x : K L (n + 1)) :
    DVR.residue S M n (map (n + 1) f x) =
      (e : ℤ) • map n (IsLocalRing.ResidueField.map j) (DVR.residue R L n x) :=
  DVR.residue_ramified_restrict_apply j f hf hπ hϖ u e hπmap n x

/-- The empty residue prefix recovers actual integer-order scaling. -/
theorem degree_zero_integer_order (x : K L 1) :
    MilnorK.K2.DVR.value S M (oneEquiv M (map 1 f x)) =
      (e : ℤ) * MilnorK.K2.DVR.value R L (oneEquiv L x) := by
  have h := congrArg (zeroEquiv (IsLocalRing.ResidueField S))
    (DVR.residue_ramified_restrict_apply j f hf hπ hϖ u e hπmap 0 x)
  simpa only [map_smul, zeroEquiv_map, DVR.zeroEquiv_residue, smul_eq_mul] using h

/-- The specialization is normalized by the stated two actual uniformizers. -/
theorem normalized_specialization (n : ℕ) (x : K L (n + 1)) :
    DVR.specializeWithUniformizer S M hϖ (n + 1) (map (n + 1) f x) =
      map (n + 1) (IsLocalRing.ResidueField.map j)
          (DVR.specializeWithUniformizer R L hπ (n + 1) x) +
        productUnit n (map n (IsLocalRing.ResidueField.map j) (DVR.residue R L n x))
          (MilnorK.K2.DVR.ramificationUnitResidue u) :=
  LinearMap.congr_fun (DVR.specialize_ramified_restrict j f hf hπ hϖ u e hπmap n) x

/-- Every repeated-uniformizer residue retains the complete sign prefix. -/
theorem repeated_uniformizers_tame (n : ℕ) :
    DVR.residue S M n (map (n + 1) f
      (symbol (fun _ => MilnorK.K2.DVR.uniformizer (K := L) hπ))) =
        (e : ℤ) • map n (IsLocalRing.ResidueField.map j)
          (symbol (fun _ => (-1 : (IsLocalRing.ResidueField R)ˣ))) := by
  rw [arbitrary_class j f hf hπ hϖ u e hπmap, DVR.residue_uniformizers]

/-- Repeated source uniformizers specialize to the sign-prefix correction,
not to zero after ramified restriction when the ramification unit is nontrivial. -/
theorem repeated_uniformizers_specialize (n : ℕ) :
    DVR.specializeWithUniformizer S M hϖ (n + 1) (map (n + 1) f
      (symbol (fun _ => MilnorK.K2.DVR.uniformizer (K := L) hπ))) =
        productUnit n (map n (IsLocalRing.ResidueField.map j)
          (symbol (fun _ => (-1 : (IsLocalRing.ResidueField R)ˣ))))
            (MilnorK.K2.DVR.ramificationUnitResidue u) := by
  rw [normalized_specialization j f hf hπ hϖ u e hπmap, DVR.residue_uniformizers]
  have hs : DVR.specializeWithUniformizer R L hπ (n + 1)
      (symbol (fun _ => MilnorK.K2.DVR.uniformizer (K := L) hπ)) = 0 :=
    specialize_symbol_uniformizer (MilnorK.K2.DVR.data (K := L) hπ)
      (MilnorK.K2.DVR.unitReductionCompatible hπ) (n + 1) _ (Fin.last n) rfl
  rw [hs, map_zero, zero_add]

/-- Applying the actual degree-two equivalences recovers the original tame map. -/
theorem original_degree_two (x : K L 2) :
    MilnorK.K2.tame (MilnorK.K2.DVR.chosenData S M) (MilnorK.K2.map f (twoEquiv L x)) =
      (e : ℤ) • MilnorK.K2.unitsLinear (IsLocalRing.ResidueField.map j)
        (MilnorK.K2.tame (MilnorK.K2.DVR.chosenData R L) (twoEquiv L x)) := by
  have h := congrArg (oneEquiv (IsLocalRing.ResidueField S))
    (DVR.residue_ramified_restrict_apply j f hf hπ hϖ u e hπmap 1 x)
  simpa [oneEquiv_map, DVR.oneEquiv_residue_one,
    twoEquiv_map, MilnorK.K2.unitsLinear] using h

omit hf hϖ [IsDomain R] [IsDiscreteValuationRing R]
  [IsDomain S] [IsDiscreteValuationRing S] in
/-- Positivity is a consequence of the actual local map and uniformizer equation. -/
theorem positive_exponent : 0 < e :=
  MilnorK.K2.DVR.ramificationIndex_pos j hπ u e hπmap

omit hπmap in
/-- Even ramification kills the repeated-pair sign by its genuine two-torsion law. -/
theorem repeated_pair_exponent_two (hπtwo : j π = (u : S) * ϖ ^ 2) :
    DVR.residue S M 1 (map 2 f
      (symbol (fun _ => MilnorK.K2.DVR.uniformizer (K := L) hπ))) = 0 := by
  rw [repeated_uniformizers_tame j f hf hπ hϖ u 2 hπtwo]
  simp only [Nat.cast_ofNat]
  rw [← map_smul]
  have hs : (2 : ℤ) • symbol (fun _ : Fin 1 => (-1 : (IsLocalRing.ResidueField R)ˣ)) = 0 := by
    apply (oneEquiv (IsLocalRing.ResidueField R)).injective
    simp only [two_smul, map_add, oneEquiv_symbol, map_zero]
    exact MilnorK.K2.residueSign_add_self (k := IsLocalRing.ResidueField R)
  rw [hs, map_zero]

omit hπmap hϖ u e in
/-- The literal unit-one, exponent-one equation recovers unramified restriction. -/
theorem unramified_consumer (hjπ : Irreducible (j π)) (n : ℕ) (x : K L (n + 1)) :
    DVR.residue S M n (map (n + 1) f x) =
      map n (IsLocalRing.ResidueField.map j) (DVR.residue R L n x) := by
  have h := DVR.residue_ramified_restrict_apply j f hf hπ hjπ 1 1 (by simp) n x
  simpa only [Nat.cast_one, one_smul] using h

end AglibTest.GeneralMilnorResidueRamifiedRestriction

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
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorResidueRamifiedRestriction]
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
  logInfo m!"Checked {names.size} ramified restriction and general Milnor declarations: \
    standard axioms only."
