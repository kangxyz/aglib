/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Aglib.KTheory.MilnorK.RationalExactness
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Consumer tests for actual all-degree rational exactness over arbitrary fields. -/

noncomputable section

open Polynomial
open MilnorK MilnorK.DegreeFiltration MilnorK.PolynomialResidue

namespace AglibTest.GeneralMilnorRationalExactness

variable {F : Type*} [Field F]

/-- Identifies the actual stage with its degree-restricted residue data. -/
def actualStageEquivalence (n d : ℕ) (hd : 0 < d) :
    actualStage F n d ≃ₗ[ℤ] DegreeResidues F n d :=
  actualStageEquiv n d hd

/-- Specializes the actual stage equivalence to degree zero. -/
def zeroDegreeStageEquivalence (d : ℕ) (hd : 0 < d) :
    actualStage F 0 d ≃ₗ[ℤ] DegreeResidues F 0 d :=
  actualStageEquiv 0 d hd

theorem actual_degree_kernel (n d : ℕ) (hd : 0 < d) (x : K (RatFunc F) (n + 1))
    (hx : x ∈ lower F (n + 1) (d + 1)) :
    degreeResidues n d x = 0 ↔ x ∈ lower F (n + 1) d :=
  degreeResidues_eq_zero_iff_mem_lower n d hd x hx

theorem off_diagonal_vanishes (n d : ℕ) (p q : DegreePlace F d) (hpq : p ≠ q)
    (x : K (AdjoinRoot p.val.val) n) :
    quotientDegreeResidues n d (degreeSection n d p x) q = 0 :=
  quotientDegreeResidues_degreeSection_of_ne n d p q hpq x

theorem all_degree_surjectivity (n : ℕ) : Function.Surjective (totalResidue (k := F) n) :=
  totalResidue_surjective n

theorem degree_zero_residue_surjectivity :
    Function.Surjective (totalResidue (k := F) 0) := totalResidue_surjective 0

theorem actual_constant_kernel (n : ℕ) (x : K (RatFunc F) (n + 1)) :
    totalResidue n x = 0 ↔
      x ∈ LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : F →+* RatFunc F)) :=
  totalResidue_eq_zero_iff_mem_constant_range n x

/-- Identifies the quotient by the constant image with the finite residue sum. -/
def actualQuotientEquivalence (n : ℕ) :
    (K (RatFunc F) (n + 1) ⧸
      LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : F →+* RatFunc F))) ≃ₗ[ℤ]
        Π₀ p : MonicIrreducible F, K (AdjoinRoot p.val) n :=
  quotientConstantEquivResidues n

theorem quotient_computes_total_residue (n : ℕ) (x : K (RatFunc F) (n + 1)) :
    quotientConstantEquivResidues n (Submodule.Quotient.mk x) = totalResidue n x :=
  quotientConstantEquivResidues_mk n x

theorem actual_short_exact_sequence (n : ℕ) :
    Function.Injective (MilnorK.map (n + 1) (RatFunc.C : F →+* RatFunc F)) ∧
      LinearMap.ker (totalResidue (k := F) n) =
        LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : F →+* RatFunc F)) ∧
      Function.Surjective (totalResidue (k := F) n) :=
  rational_short_exact n

theorem characteristic_two_surjectivity (n : ℕ) :
    Function.Surjective (totalResidue (k := ZMod 2) n) := totalResidue_surjective n

/-- Each original residue coordinate is lifted, with no uniform bound on residue fields. -/
theorem lift_all_coordinates (n : ℕ)
    (y : Π₀ p : MonicIrreducible F, K (AdjoinRoot p.val) n) :
    ∃ x : K (RatFunc F) (n + 1), ∀ p : MonicIrreducible F, residueAt p.val n x = y p := by
  obtain ⟨x, hx⟩ := totalResidue_surjective n y
  exact ⟨x, fun p => DFunLike.congr_fun hx p⟩

/-- Surjectivity preserves a specified polynomial degree bound. -/
theorem lift_with_degree_bound (n d : ℕ)
    (y : Π₀ p : MonicIrreducible F, K (AdjoinRoot p.val) n)
    (hy : ∀ p : MonicIrreducible F, d ≤ p.val.natDegree → y p = 0) :
    ∃ x ∈ lower F (n + 1) d, totalResidue n x = y :=
  exists_mem_lower_totalResidue_eq n d y hy

/-- An everywhere unramified class is an actual constant restriction. -/
theorem zero_residues_iff_constant_image (n : ℕ) (x : K (RatFunc F) (n + 1)) :
    (∀ p : MonicIrreducible F, residueAt p.val n x = 0) ↔
      ∃ c : K F (n + 1), MilnorK.map (n + 1) (RatFunc.C : F →+* RatFunc F) c = x := by
  rw [← totalResidue_eq_zero_iff, totalResidue_eq_zero_iff_mem_constant_range]
  rfl

/-- The quotient equivalence computes each original finite-place residue. -/
theorem quotient_coordinate (n : ℕ) (x : K (RatFunc F) (n + 1))
    (p : MonicIrreducible F) :
    quotientConstantEquivResidues n (Submodule.Quotient.mk x) p = residueAt p.val n x := by
  rw [quotientConstantEquivResidues_mk, totalResidue_apply]

end AglibTest.GeneralMilnorRationalExactness

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.RingTheory.PolynomialLocalResidue]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "The rational exactness audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK, `MilnorK.K2,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue]
  let consumerPrefix := `AglibTest.GeneralMilnorRationalExactness
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
  for name in names.toArray do
    if selected name then
      unless (env.checked.get.find? name).isSome do
        throwError "General rational exactness declaration {name} is absent \
          from the kernel environment"
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Verified the actual all-degree polynomial stages and rational exactness, \
    including private helpers: standard Lean logical foundations only."
