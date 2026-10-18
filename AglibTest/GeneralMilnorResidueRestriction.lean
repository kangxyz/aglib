/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Restriction
import Lean.Util.CollectAxioms

/-! Direct consumers of actual all-degree unramified restriction. The local
ring map, commuting fraction-field square, and preservation of one actual
uniformizer are explicit; valuation or residue compatibility is not assumed.
Legacy imports make every audited proof available to the axiom collector. -/

open MilnorK

namespace AglibTest.GeneralMilnorResidueRestriction

variable {R S L M : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra R L] [IsFractionRing R L]
  [Field M] [Algebra S M] [IsFractionRing S M]
  (j : R →+* S) [IsLocalHom j] (f : L →+* M)
  (hf : ∀ r : R, f (algebraMap R L r) = algebraMap S M (j r))

include hf

/-- No symbol or valuation restriction remains on the input quotient class. -/
theorem arbitrary_class {π : R} (hπ : Irreducible π) (hjπ : Irreducible (j π))
    (n : ℕ) (x : K L (n + 1)) :
    map n (IsLocalRing.ResidueField.map j) (DVR.residue R L n x) =
      DVR.residue S M n (map (n + 1) f x) :=
  DVR.residue_restrict_apply j f hf hπ hjπ n x

/-- The empty target tuple recovers preservation of normalized integer order. -/
theorem degree_zero_integer_value {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (x : K L 1) :
    MilnorK.K2.DVR.value S M (oneEquiv M (map 1 f x)) =
      MilnorK.K2.DVR.value R L (oneEquiv L x) := by
  have h := congrArg (zeroEquiv (IsLocalRing.ResidueField S))
    (DVR.residue_restrict_apply j f hf hπ hjπ 0 x)
  simpa only [zeroEquiv_map, DVR.zeroEquiv_residue] using h.symm

/-- Applying the already proved degree-two comparison recovers the original
Milnor K3-to-K2 residue square on every all-degree input class. -/
theorem degree_two_original_residue {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (x : K L 3) :
    MilnorK.K2.map (IsLocalRing.ResidueField.map j)
        (MilnorK.K3.DVR.residue R L (threeEquiv L x)) =
      MilnorK.K3.DVR.residue S M (MilnorK.K3.map f (threeEquiv L x)) := by
  have h := congrArg (twoEquiv (IsLocalRing.ResidueField S))
    (DVR.residue_restrict_apply j f hf hπ hjπ 2 x)
  simpa only [Nat.reduceAdd, twoEquiv_map, DVR.twoEquiv_residue_two, threeEquiv_map] using h

/-- Arbitrary poles and repeated uniformizers require no new hypotheses. -/
theorem poles_and_repeated_uniformizers {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (n : ℕ) :
    map n (IsLocalRing.ResidueField.map j)
        (DVR.residue R L n
          (symbol (Function.update
            (fun _ : Fin (n + 1) => MilnorK.K2.DVR.uniformizer (K := L) hπ)
            (Fin.last n) (MilnorK.K2.DVR.uniformizer (K := L) hπ ^ (-3 : ℤ))))) =
      DVR.residue S M n
        (map (n + 1) f
          (symbol (Function.update
            (fun _ : Fin (n + 1) => MilnorK.K2.DVR.uniformizer (K := L) hπ)
            (Fin.last n) (MilnorK.K2.DVR.uniformizer (K := L) hπ ^ (-3 : ℤ))))) :=
  DVR.residue_restrict_apply j f hf hπ hjπ n _

end AglibTest.GeneralMilnorResidueRestriction

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
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorResidueRestriction]
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
  logInfo m!"Checked {names.size} unramified restriction and general Milnor declarations: \
    standard axioms only."
