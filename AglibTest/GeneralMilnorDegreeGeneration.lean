/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.DegreeGeneration
import Mathlib.Tactic.FinCases
import Lean.Util.CollectAxioms

/-!
# Consumers of the all-degree polynomial generation theorem

The final-slot top generators, arbitrary positive degree bound, degree-one
edge case, and repeated top entries are tested in the original Milnor quotient.
The audit includes every imported general-Milnor declaration and private helper.
-/

open MilnorK MilnorK.DegreeFiltration Polynomial

namespace AglibTest.GeneralMilnorDegreeGeneration

universe u
variable (F : Type u) [Field F] (n : ℕ)

/-- The actual degree stage has precisely the final-slot irreducible generators. -/
theorem general_degree_step (d : ℕ) (hd : 0 < d) :
    lower F (n + 1) (d + 1) =
      lower F (n + 1) d ⊔ Submodule.span ℤ (topGenerators F n d) := lower_succ_eq d hd

/-- The argument includes degree-one Milnor theory, where the small tuple is empty. -/
theorem degree_one_step (d : ℕ) (hd : 0 < d) :
    lower F 1 (d + 1) = lower F 1 d ⊔ Submodule.span ℤ (topGenerators F 0 d) :=
  lower_succ_eq d hd

/-- Individually bounded coordinates suffice without a bound on their sum of degrees. -/
theorem individual_bounds (d : ℕ) (hd : 0 < d)
    (a : Fin (n + 1) → F[X]) (ha : ∀ i, a i ≠ 0)
    (hdeg : ∀ i, (a i).natDegree ≤ d) :
    symbol (polynomialTuple a ha) ∈ generatedStage F n d :=
  polynomial_symbol_mem_generatedStage d hd a ha hdeg

variable {F}

/-- A fourth-degree symbol with four repeated top entries is reduced with its sign terms. -/
theorem four_repeated_top (d : ℕ) (hd : 0 < d) (p : F[X])
    (hp : p.Monic) (hi : Irreducible p) (hdeg : p.natDegree = d) :
    symbol (fun _ : Fin 4 => polynomialUnit F p hp.ne_zero) ∈ generatedStage F 3 d := by
  exact atomic_tuple_mem d hd (fun _ => p) (fun _ => hp.ne_zero)
    (fun _ => Or.inr ⟨hp, hi, hdeg⟩)

/-- A first-slot top entry in degree four can be moved to the final-slot generating family. -/
theorem four_first_top (d : ℕ) (p a b c : F[X])
    (hp : p.Monic) (hi : Irreducible p) (hdeg : p.natDegree = d)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hadeg : a.natDegree < d) (hbdeg : b.natDegree < d) (hcdeg : c.natDegree < d) :
    symbol ![polynomialUnit F p hp.ne_zero, polynomialUnit F a ha,
      polynomialUnit F b hb, polynomialUnit F c hc] ∈ generatedStage F 3 d := by
  let v : Fin 4 → F[X] := ![p, a, b, c]
  have hv : ∀ i, v i ≠ 0 := by
    intro i
    fin_cases i <;> simp [v, hp.ne_zero, ha, hb, hc]
  have h := polynomial_symbol_mem_generatedStage_one_top d v hv 0 hp hi hdeg (by
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · simpa [v] using hadeg
    · simpa [v] using hbdeg
    · simpa [v] using hcdeg)
  have heq : polynomialTuple v hv = ![polynomialUnit F p hp.ne_zero,
      polynomialUnit F a ha, polynomialUnit F b hb, polynomialUnit F c hc] := by
    funext i
    fin_cases i <;> simp [polynomialTuple, v]
  rwa [heq] at h

end AglibTest.GeneralMilnorDegreeGeneration

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
    throwError "The general Milnor degree generation audit requires legacy imports"
  let libraryPrefix := `MilnorK
  let consumerPrefix := `AglibTest.GeneralMilnorDegreeGeneration
  let isLibrary (name : Name) : Bool := libraryPrefix.isPrefixOf name
  let selectedDeclaration (name : Name) : Bool :=
    let libraryOrigin := match env.getModuleIdxFor? name with
      | some index => isLibraryModule env.header.moduleNames[index.toNat]!
      | none => false
    libraryOrigin || isLibrary name || consumerPrefix.isPrefixOf name
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for i in [:env.header.moduleNames.size] do
    let libraryOrigin := isLibraryModule env.header.moduleNames[i]!
    for name in env.header.moduleData[i]!.constNames do
      if libraryOrigin || isLibrary name then
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    if selected name then
      unless (env.checked.get.find? name).isSome do
        throwError "General Milnor declaration {name} is missing from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} general Milnor degree generation and consumer declarations, \
    including private helpers: only standard Lean logical foundations."
