/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.DegreeFiltration
import Lean.Util.CollectAxioms

/-!
# Consumers of the actual all-degree polynomial filtration

These tests use arbitrary fields and the original quotient `K`, with no norm,
motivic comparison, or rational exactness assumptions. The degree-zero test
checks that the empty-tuple edge case is included.
-/

open MilnorK MilnorK.DegreeFiltration Polynomial

namespace AglibTest.GeneralMilnorDegreeFiltration

universe u
variable (F : Type u) [Field F] (r : ℕ)

/-- Every actual quotient class has a finite polynomial degree bound. -/
theorem arbitrary_class_bounded (x : K (RatFunc F) r) :
    ∃ d, x ∈ lower F r d := exists_mem_lower x

/-- The same exhaustion includes the integer-valued degree-zero group. -/
theorem empty_degree_bounded (x : K (RatFunc F) 0) :
    ∃ d, x ∈ lower F 0 d := exists_mem_lower x

/-- Every individually bounded tuple is included, without a bound on their total degrees. -/
theorem individually_bounded (d : ℕ) (a : Fin r → F[X])
    (ha : ∀ i, a i ≠ 0) (hdeg : ∀ i, (a i).natDegree < d) :
    symbol (polynomialTuple a ha) ∈ lower F r d := polynomial_symbol_mem_lower d a ha hdeg

/-- The filtration is increasing in arbitrary Milnor degree. -/
theorem increasing {d e : ℕ} (h : d ≤ e) : lower F r d ≤ lower F r e := lower_mono h

/-- The first stage is exactly the literal constant-field map's range. -/
theorem first_stage :
    lower F r 1 = LinearMap.range (MilnorK.map r (RatFunc.C : F →+* RatFunc F)) :=
  lower_one_eq_constant_range

/-- The supremum of the actual stages is the whole original quotient. -/
theorem exhaustive : (⨆ d, lower F r d) = ⊤ := iSup_lower_eq_top

variable {F} (p : F[X]) [Fact (Irreducible p)]

omit [Fact (Irreducible p)] in
/-- The correction for reduced multiplication is genuinely smaller-degree and nonzero. -/
theorem smaller_correction (hp : p.Monic) (a b : F[X])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (hbdeg : b.natDegree < p.natDegree)
    (hne : a * b ≠ (a * b) %ₘ p) :
    ∃ f : F[X], f ≠ 0 ∧ f.natDegree < p.natDegree ∧ (a * b) %ₘ p = a * b + f * p :=
  reduced_mul_correction p hp a b ha hb hadeg hbdeg hne

/-- A reduced sum equal to one in the residue field is already literally one. -/
theorem literal_reduced_sum (hp : p.Monic) (a b : F[X])
    (hadeg : a.natDegree < p.natDegree) (hbdeg : b.natDegree < p.natDegree)
    (h : AdjoinRoot.mk p a + AdjoinRoot.mk p b = 1) : a + b = 1 :=
  reduced_add_eq_one p hp a b hadeg hbdeg h

end AglibTest.GeneralMilnorDegreeFiltration

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
    throwError "The general Milnor degree filtration audit requires legacy imports"
  let libraryPrefix := `MilnorK
  let consumerPrefix := `AglibTest.GeneralMilnorDegreeFiltration
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
  logInfo m!"Audited {count} general Milnor degree filtration and consumer declarations, \
    including private helpers: only standard Lean logical foundations."
