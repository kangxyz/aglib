/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.DegreeFiltration
import Lean.Util.CollectAxioms

/-!
# Consumers and rejecting audit for reduced polynomial multiplication

The target is the quotient of actual rational-function K₃ by the integer span
of literal three-polynomial symbols with all degrees below the modulus degree.
The tests check nonvanishing, derived correction degrees, both multiplication
coordinates, and residue-field Steinberg. Legacy imports expose all private
helpers to a standard-logical-axioms-only dependency audit.
-/

open Polynomial
open MilnorK.K2 MilnorK.K3
open MilnorK.K3.PolynomialResidue
open MilnorK.K3.DegreeFiltration

noncomputable section

namespace AglibTest.MilnorK3DegreeFiltration

variable {k : Type*} [Field k]

/-- The lower stage uses actual polynomial symbols in the original K₃ group. -/
theorem actual_lower_stage (d : ℕ) :
    lower k d = Submodule.span ℤ
      {x | ∃ (a b c : k[X]) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0),
        a.natDegree < d ∧ b.natDegree < d ∧ c.natDegree < d ∧
        x = symbol3 (polynomialUnit a ha) (polynomialUnit b hb) (polynomialUnit c hc)} := rfl

/-- Monotonicity acts on all actual K₃ classes in the lower stage. -/
theorem lower_stage_inclusion {d e : ℕ} (hde : d ≤ e) (x : MilnorK.K3.Group (RatFunc k))
    (hx : x ∈ lower k d) : x ∈ lower k e := lower_mono hde hx

/-- The correction degree is derived by division, without an assumed filtration relation. -/
theorem derived_correction (p : k[X]) (hp : p.Monic) (a a' : k[X])
    (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (ha'deg : a'.natDegree < p.natDegree)
    (hne : a * a' ≠ (a * a') %ₘ p) :
    ∃ f : k[X], f ≠ 0 ∧ f.natDegree < p.natDegree ∧
      (a * a') %ₘ p = a * a' + f * p :=
  reduced_mul_correction p hp a a' ha ha' hadeg ha'deg hne

variable (p : k[X]) [Fact (Irreducible p)]

/-- Both nonzero and smaller-degree properties of the product remainder are derived. -/
theorem nonzero_reduced_product (hp : p.Monic) (a a' : k[X])
    (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (ha'deg : a'.natDegree < p.natDegree) :
    (a * a') %ₘ p ≠ 0 ∧ ((a * a') %ₘ p).natDegree < p.natDegree :=
  ⟨reduced_mul_ne_zero p hp a a' ha ha' hadeg ha'deg,
    reduced_mul_natDegree_lt p hp a a'⟩

/-- The middle-coordinate identity is an equality in the actual lower-stage quotient. -/
theorem middle_coordinate_in_actual_quotient (hp : p.Monic) (a a' b : k[X])
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (ha'deg : a'.natDegree < p.natDegree)
    (hbdeg : b.natDegree < p.natDegree) :
    (lower k p.natDegree).mkQ
        (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
          (polynomialUnit a ha) (polynomialUnit b hb)) +
      (lower k p.natDegree).mkQ
        (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
          (polynomialUnit a' ha') (polynomialUnit b hb)) =
      (lower k p.natDegree).mkQ
        (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
          (polynomialUnit ((a * a') %ₘ p)
            (reduced_mul_ne_zero p hp a a' ha ha' hadeg ha'deg)) (polynomialUnit b hb)) := by
  rw [← map_add]
  exact (Submodule.Quotient.eq _).mpr
    (reduced_mul_middle_mem_lower p hp a a' b ha ha' hb hadeg ha'deg hbdeg)

/-- The last-coordinate identity is an equality in the same actual quotient. -/
theorem right_coordinate_in_actual_quotient (hp : p.Monic) (a b b' : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (hbdeg : b.natDegree < p.natDegree)
    (hb'deg : b'.natDegree < p.natDegree) :
    (lower k p.natDegree).mkQ
        (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
          (polynomialUnit a ha) (polynomialUnit b hb)) +
      (lower k p.natDegree).mkQ
        (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
          (polynomialUnit a ha) (polynomialUnit b' hb')) =
      (lower k p.natDegree).mkQ
        (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
          (polynomialUnit a ha) (polynomialUnit ((b * b') %ₘ p)
            (reduced_mul_ne_zero p hp b b' hb hb' hbdeg hb'deg))) := by
  rw [← map_add]
  exact (Submodule.Quotient.eq _).mpr
    (reduced_mul_right_mem_lower p hp a b b' ha hb hb' hadeg hbdeg hb'deg)

/-- Residue-field Steinberg descends without assuming a literal polynomial sum. -/
theorem steinberg_in_actual_quotient (hp : p.Monic) (a b : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (hbdeg : b.natDegree < p.natDegree)
    (hsum : AdjoinRoot.mk p a + AdjoinRoot.mk p b = 1) :
    (lower k p.natDegree).mkQ
      (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
        (polynomialUnit a ha) (polynomialUnit b hb)) = 0 := by
  rw [reduced_steinberg p hp a b ha hb hadeg hbdeg hsum, map_zero]

/-- The residue-field equation is proved to be an exact polynomial equation. -/
theorem literal_reduced_steinberg_sum (hp : p.Monic) (a b : k[X])
    (hadeg : a.natDegree < p.natDegree) (hbdeg : b.natDegree < p.natDegree)
    (hsum : AdjoinRoot.mk p a + AdjoinRoot.mk p b = 1) : a + b = 1 :=
  reduced_add_eq_one p hp a b hadeg hbdeg hsum

end AglibTest.MilnorK3DegreeFiltration

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.RingTheory.PolynomialLocalResidue]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "The Milnor K₃ filtration audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue]
  let consumerPrefix := `AglibTest.MilnorK3DegreeFiltration
  let isLibrary (name : Name) : Bool := libraryPrefixes.any (·.isPrefixOf name)
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
        throwError "Milnor K₃ degree filtration declaration {name} is absent from \
          the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃, polynomial local residue, and degree filtration \
    declarations, including private helpers: only standard Lean logical foundations."
