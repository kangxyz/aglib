/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.StageEquivalence
import Lean.Util.CollectAxioms

/-!
# Consumers and rejecting audit for the actual degree-stage equivalence

The source is the literal image of the next polynomial span in the quotient
by the preceding span. The target is the finite dependent sum of the original
residue-field K₂ groups, with exact degree indexing and integer scalars. The
equivalence requires positive degree and consumes the proved generation theorem.
-/

open Polynomial
open MilnorK.K2 MilnorK.K3
open MilnorK.K3.PolynomialResidue
open MilnorK.K3.DegreeFiltration

noncomputable section

namespace AglibTest.MilnorK3StageEquivalence

variable {k : Type*} [Field k]

/-- No formal replacement for either the actual stage or original residue groups occurs. -/
def literal_integer_linear_equivalence (d : ℕ) (hd : 0 < d) :
    ((lower k (d + 1)).map (lower k d).mkQ) ≃ₗ[ℤ]
      Π₀ p : {p : MonicIrreducible k // p.val.natDegree = d}, MilnorK.K2.Group (AdjoinRoot p.val.val) :=
  actualStageEquiv d hd

/-- Restriction of the original finite-support total residue supplies every coordinate. -/
theorem coordinate_is_original_residue (d : ℕ) (x : MilnorK.K3.Group (RatFunc k))
    (p : DegreePlace k d) : degreeResidues d x p = totalResidue x p.val := rfl

/-- Equal-degree off-diagonal vanishing is valid on every original K₂ class. -/
theorem other_place_vanishes (d : ℕ) (p q : DegreePlace k d) (hpq : p ≠ q)
    (x : MilnorK.K2.Group (AdjoinRoot p.val.val)) :
    quotientDegreeResidues d (degreeSection d p x) q = 0 :=
  quotientDegreeResidues_degreeSection_of_ne d p q hpq x

/-- Every section lies in the actual quotient image, before invoking stage generation. -/
theorem section_has_actual_representative (d : ℕ) (p : DegreePlace k d)
    (x : MilnorK.K2.Group (AdjoinRoot p.val.val)) :
    ∃ y ∈ lower k (d + 1), (lower k d).mkQ y = degreeSection d p x :=
  Submodule.mem_map.mp (degreeSection_mem_actualStage d p x)

/-- The sum-residue identity is checked on arbitrary finite-support original classes. -/
theorem residue_recovers_every_finite_input (d : ℕ) (x : DegreeResidues k d) :
    quotientDegreeResidues d (degreeSectionSum d x) = x :=
  quotientDegreeResidues_degreeSectionSum d x

/-- The opposite identity uses the proved positive-degree generation theorem. -/
theorem sections_recover_every_actual_class (d : ℕ) (hd : 0 < d)
    (x : MilnorK.K3.Group (RatFunc k) ⧸ lower k d) (hx : x ∈ actualStage k d) :
    degreeSectionSum d (quotientDegreeResidues d x) = x :=
  degreeSectionSum_quotientDegreeResidues d hd x hx

/-- The forward equivalence computes the original residue on every stage representative. -/
theorem equivalence_coordinate (d : ℕ) (hd : 0 < d) (x : MilnorK.K3.Group (RatFunc k))
    (hx : x ∈ lower k (d + 1)) (p : DegreePlace k d) :
    actualStageEquiv d hd
      ⟨(lower k d).mkQ x, Submodule.mem_map.mpr ⟨x, hx, rfl⟩⟩ p = residueAt p.val.val x :=
  actualStageEquiv_mkQ_apply d hd x hx p

/-- The inverse is the original finite sum, not a choice of unrelated preimages. -/
theorem inverse_is_canonical_finite_sum (d : ℕ) (hd : 0 < d) (x : DegreeResidues k d) :
    ((actualStageEquiv d hd).symm x : MilnorK.K3.Group (RatFunc k) ⧸ lower k d) = degreeSectionSum d x :=
  actualStageEquiv_symm_coe d hd x

/-- At one residue-field symbol the inverse is the literal canonical triple symbol. -/
theorem inverse_single_symbol (d : ℕ) (hd : 0 < d) [DecidableEq (DegreePlace k d)]
    (p : DegreePlace k d) (a b : (AdjoinRoot p.val.val)ˣ) :
    ((actualStageEquiv d hd).symm (DFinsupp.single p (symbol a b)) :
      MilnorK.K3.Group (RatFunc k) ⧸ lower k d) =
      (lower k d).mkQ
        (symbol3 (polynomialUnit p.val.val p.val.property.2.ne_zero)
          (polynomialUnit (AdjoinRoot.modByMonicHom p.val.property.1 (a : AdjoinRoot p.val.val))
            (reducedRepresentative_ne_zero p.val.val p.val.property.1 a))
          (polynomialUnit (AdjoinRoot.modByMonicHom p.val.property.1 (b : AdjoinRoot p.val.val))
            (reducedRepresentative_ne_zero p.val.val p.val.property.1 b))) := by
  rw [actualStageEquiv_symm_coe, degreeSectionSum_single, degreeSection_symbol]
  rfl

/-- The degree-stage kernel is precisely the actual preceding polynomial span. -/
theorem stage_kernel (d : ℕ) (hd : 0 < d) (x : MilnorK.K3.Group (RatFunc k))
    (hx : x ∈ lower k (d + 1)) : degreeResidues d x = 0 ↔ x ∈ lower k d :=
  degreeResidues_eq_zero_iff_mem_lower d hd x hx

/-- Both inverse identities hold as integer-linear maps of the actual groups. -/
theorem both_linear_inverse_identities (d : ℕ) (hd : 0 < d) :
    (actualStageResidues d).comp (actualStageSectionSum (k := k) d) = LinearMap.id ∧
      (actualStageSectionSum d).comp (actualStageResidues (k := k) d) = LinearMap.id :=
  ⟨actualStageResidues_comp_actualStageSectionSum d,
    actualStageSectionSum_comp_actualStageResidues d hd⟩

end AglibTest.MilnorK3StageEquivalence

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
    throwError "The Milnor K₃ stage equivalence audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue]
  let consumerPrefix := `AglibTest.MilnorK3StageEquivalence
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
        throwError "Milnor K₃ stage equivalence declaration {name} is absent \
          from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃, polynomial local residue, and stage \
    equivalence declarations, including private helpers: only standard Lean logical foundations."
