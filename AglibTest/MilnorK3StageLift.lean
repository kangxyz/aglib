/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.StageLift
import Lean.Util.CollectAxioms

/-!
# Consumers and rejecting audit for the actual polynomial stage section

These consumers preserve the original K₂ tensor quotient, original rational
K₃ group, integer scalars, and actual lower-degree polynomial span. They check
canonical reduced representatives, literal symbol values, the descended actual
residue, and the section identity on all K₂ classes. The final audit rejects
nonstandard axioms throughout the imported Milnor and polynomial-local code,
including private helpers exposed by legacy imports.
-/

open Polynomial
open MilnorK.K2 MilnorK.K3
open MilnorK.K3.PolynomialResidue
open MilnorK.K3.DegreeFiltration

noncomputable section

namespace AglibTest.MilnorK3StageLift

variable {k : Type*} [Field k]
variable (p : k[X]) [Fact (Irreducible p)]

/-- The lift uses the original residue-field K₂ and the actual lower-stage quotient. -/
def actualIntegerLinearSection (hp : p.Monic) :
    MilnorK.K2.Group (AdjoinRoot p) →ₗ[ℤ] MilnorK.K3.Group (RatFunc k) ⧸ lower k p.natDegree := stageLift p hp

/-- Representatives come directly from the pinned canonical polynomial reduction map. -/
theorem canonical_representative (hp : p.Monic) (a : (AdjoinRoot p)ˣ) :
    reducedRepresentative p hp a = AdjoinRoot.modByMonicHom hp (a : AdjoinRoot p) := rfl

/-- The chosen polynomial is both nonzero and strictly smaller in degree. -/
theorem reduced_representative_bounds (hp : p.Monic) (a : (AdjoinRoot p)ˣ) :
    reducedRepresentative p hp a ≠ 0 ∧
      (reducedRepresentative p hp a).natDegree < p.natDegree :=
  ⟨reducedRepresentative_ne_zero p hp a, reducedRepresentative_natDegree_lt p hp a⟩

/-- Polynomial reduction recovers the literal original residue-field unit. -/
theorem representative_recovers_unit (hp : p.Monic) (a : (AdjoinRoot p)ˣ) :
    AdjoinRoot.mk p (reducedRepresentative p hp a) = (a : AdjoinRoot p) :=
  mk_reducedRepresentative p hp a

/-- The original K₂ symbol goes to its literal triple-symbol quotient class. -/
theorem literal_canonical_symbol (hp : p.Monic) (a b : (AdjoinRoot p)ˣ) :
    stageLift p hp (symbol a b) =
      (lower k p.natDegree).mkQ
        (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
          (polynomialUnit (AdjoinRoot.modByMonicHom hp (a : AdjoinRoot p))
            (reducedRepresentative_ne_zero p hp a))
          (polynomialUnit (AdjoinRoot.modByMonicHom hp (b : AdjoinRoot p))
            (reducedRepresentative_ne_zero p hp b))) := stageLift_symbol p hp a b

/-- An arbitrary pair of already reduced polynomials gives the expected lift. -/
theorem literal_polynomial_symbol (hp : p.Monic) (a b : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (hbdeg : b.natDegree < p.natDegree) :
    stageLift p hp (symbol
      (quotientUnit p a (hp.not_dvd_of_natDegree_lt ha hadeg))
      (quotientUnit p b (hp.not_dvd_of_natDegree_lt hb hbdeg))) =
      (lower k p.natDegree).mkQ
        (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
          (polynomialUnit a ha) (polynomialUnit b hb)) :=
  stageLift_reduced p hp a b ha hb hadeg hbdeg

/-- Integer linearity holds on arbitrary original K₂ classes. -/
theorem original_K2_integer_linearity (hp : p.Monic) (n : ℤ)
    (x y : MilnorK.K2.Group (AdjoinRoot p)) :
    stageLift p hp (n • x + y) = n • stageLift p hp x + stageLift p hp y := by
  rw [map_add, map_smul]

/-- No smaller-degree polynomial symbol has a nonzero residue at this place. -/
theorem residue_kills_all_lower_classes (hp : p.Monic) (x : MilnorK.K3.Group (RatFunc k))
    (hx : x ∈ lower k p.natDegree) : residueAt p x = 0 :=
  lower_le_ker_residueAt p hp hx

/-- The quotient residue is the actual polynomial-local residue, on every class. -/
theorem descended_residue_is_actual (hp : p.Monic) (x : MilnorK.K3.Group (RatFunc k)) :
    stageResidue p hp ((lower k p.natDegree).mkQ x) = residueAt p x :=
  stageResidue_mkQ p hp x

/-- The two constructed integer-linear maps compose to the identity. -/
theorem section_as_linear_maps (hp : p.Monic) :
    (stageResidue p hp).comp (stageLift p hp) = LinearMap.id :=
  stageResidue_comp_stageLift p hp

/-- The section holds on every original tensor-quotient class, without representative choices. -/
theorem section_on_every_original_class (hp : p.Monic) (x : MilnorK.K2.Group (AdjoinRoot p)) :
    stageResidue p hp (stageLift p hp x) = x := stageResidue_stageLift p hp x

/-- Equality of the lifted classes reflects equality in the original K₂ group. -/
theorem stage_lift_reflects_equality (hp : p.Monic) (x y : MilnorK.K2.Group (AdjoinRoot p))
    (h : stageLift p hp x = stageLift p hp y) : x = y := stageLift_injective p hp h

/-- Every original K₂ class has a preimage under the descended actual residue. -/
theorem actual_stage_residue_surjects (hp : p.Monic) (x : MilnorK.K2.Group (AdjoinRoot p)) :
    ∃ y : MilnorK.K3.Group (RatFunc k) ⧸ lower k p.natDegree, stageResidue p hp y = x :=
  stageResidue_surjective p hp x

end AglibTest.MilnorK3StageLift

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
    throwError "The Milnor K₃ stage lift audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue]
  let consumerPrefix := `AglibTest.MilnorK3StageLift
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
        throwError "Milnor K₃ stage lift declaration {name} is absent from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃, polynomial local residue, and stage lift declarations, \
    including private helpers: only standard Lean logical foundations."
