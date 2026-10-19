/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.PolynomialNorm
import Lean.Util.CollectAxioms

/-!
# Consumers and rejecting audit for actual polynomial-presentation norms

The source, target, finite residues, and infinity residue are the original
Milnor groups and actual maps. No assumed norm, separability, injectivity of
constant K₃, presentation independence, or extension tower law occurs.
-/

open Polynomial
open MilnorK.K2 MilnorK.K3
open MilnorK.K3.PolynomialResidue
open MilnorK.K3.PolynomialNorm

noncomputable section

namespace AglibTest.MilnorK3PolynomialNorm

variable {k : Type*} [Field k]

/-- The finite-place norm has exactly the original source and target groups. -/
def originalPolynomialNorm (p : MonicIrreducible k) :
    MilnorK.K2.Group (AdjoinRoot p.val) →ₗ[ℤ] MilnorK.K2.Group k := polynomialNorm p

/-- The polynomial norm target is literally the original tensor/Steinberg quotient. -/
theorem original_target :
    MilnorK.K2.Group k = (TensorProduct ℤ (Additive kˣ) (Additive kˣ) ⧸ steinbergSpan k) := rfl

/-- The polynomial norm source is literally the original residue-field quotient. -/
theorem original_source (p : MonicIrreducible k) :
    MilnorK.K2.Group (AdjoinRoot p.val) =
      (TensorProduct ℤ (Additive (AdjoinRoot p.val)ˣ) (Additive (AdjoinRoot p.val)ˣ) ⧸
        steinbergSpan (AdjoinRoot p.val)) := rfl

/-- The quotient used for descent is by the constant image, without injectivity. -/
def actualQuotientDescent :
    (MilnorK.K3.Group (RatFunc k) ⧸
      LinearMap.range (MilnorK.K3.map (RatFunc.C : k →+* RatFunc k)))
        →ₗ[ℤ] MilnorK.K2.Group k := quotientNorm

/-- The actual total norm has the original dependent finite sum as its domain. -/
def originalTotalNorm :
    (Π₀ p : MonicIrreducible k, MilnorK.K2.Group (AdjoinRoot p.val)) →ₗ[ℤ] MilnorK.K2.Group k := totalNorm

/-- The quotient descent computes the actual negative infinity residue. -/
theorem actual_descent_value (x : MilnorK.K3.Group (RatFunc k)) :
    quotientNorm (Submodule.Quotient.mk x) = -InfinityResidue.residue k x :=
  quotientNorm_mk x

/-- The total norm identity holds for every actual rational-function K₃ class. -/
theorem total_actual_reciprocity (x : MilnorK.K3.Group (RatFunc k)) :
    totalNorm (totalResidue x) + InfinityResidue.residue k x = 0 := by
  rw [totalNorm_totalResidue, neg_add_cancel]

/-- Any lift of a finite residue vector computes the same actual total norm. -/
theorem value_of_any_actual_lift
    (y : Π₀ p : MonicIrreducible k, MilnorK.K2.Group (AdjoinRoot p.val))
    (x : MilnorK.K3.Group (RatFunc k)) (hx : totalResidue x = y) :
    totalNorm y = -InfinityResidue.residue k x := by
  rw [← hx, totalNorm_totalResidue]

/-- The actual residue relation uniquely determines the total norm. -/
theorem uniqueness_from_original_residues
    (f : (Π₀ p : MonicIrreducible k, MilnorK.K2.Group (AdjoinRoot p.val)) →ₗ[ℤ] MilnorK.K2.Group k)
    (hf : ∀ x : MilnorK.K3.Group (RatFunc k), f (totalResidue x) = -InfinityResidue.residue k x) :
    f = totalNorm := totalNorm_unique f hf

open scoped Classical in
/-- The single-place norm is its genuine coordinate in the total norm. -/
theorem single_coordinate_norm (p : MonicIrreducible k) (x : MilnorK.K2.Group (AdjoinRoot p.val)) :
    totalNorm (DFinsupp.single p x) = polynomialNorm p x := totalNorm_single p x

open scoped Classical in
/-- Every single-place original K₂ class has an actual K₃ lift computing its norm. -/
theorem single_place_actual_lift (p : MonicIrreducible k) (y : MilnorK.K2.Group (AdjoinRoot p.val)) :
    ∃ x : MilnorK.K3.Group (RatFunc k), totalResidue x = DFinsupp.single p y ∧
      polynomialNorm p y = -InfinityResidue.residue k x := by
  obtain ⟨x, hx⟩ := totalResidue_surjective (DFinsupp.single p y)
  refine ⟨x, hx, ?_⟩
  rw [← totalNorm_single, ← hx, totalNorm_totalResidue]

open scoped Classical in
/-- Finite reciprocity sums the actual residues over their genuine finite support. -/
theorem original_finite_sum_reciprocity (x : MilnorK.K3.Group (RatFunc k)) :
    (∑ p ∈ (totalResidue x).support, polynomialNorm p (residueAt p.val x)) +
      InfinityResidue.residue k x = 0 := finite_rational_reciprocity x

/-- The degree formula holds for every class of the original constant-field K₂. -/
theorem original_constant_degree (p : MonicIrreducible k) (x : MilnorK.K2.Group k) :
    polynomialNorm p
      (MilnorK.K2.map (algebraMap k (AdjoinRoot p.val)) x) =
      (p.val.natDegree : ℤ) • x := polynomialNorm_map_constants p x

/-- The positive degree formula includes symbols of literal constant-field units. -/
theorem original_constant_symbol_degree (p : MonicIrreducible k) (a b : kˣ) :
    polynomialNorm p
      (symbol (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom a)
        (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      (p.val.natDegree : ℤ) • symbol a b := polynomialNorm_map_constant_symbol p a b

/-- At a degree-one presentation the norm is the identity on constant K₂ images. -/
theorem degree_one_constants (p : MonicIrreducible k) (hp : p.val.natDegree = 1)
    (x : MilnorK.K2.Group k) :
    polynomialNorm p
      (MilnorK.K2.map (algebraMap k (AdjoinRoot p.val)) x) = x := by
  rw [polynomialNorm_map_constants, hp, Nat.cast_one, one_smul]

/-- Polynomial norms remain integer-linear on arbitrary residue-field classes. -/
theorem original_norm_integer_linear (p : MonicIrreducible k) (n : ℤ)
    (x y : MilnorK.K2.Group (AdjoinRoot p.val)) :
    polynomialNorm p (n • x - y) = n • polynomialNorm p x - polynomialNorm p y := by
  rw [map_sub, map_smul]

end AglibTest.MilnorK3PolynomialNorm

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.RingTheory.PolynomialLocalResidue]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "The polynomial norm audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue,
    `Motivic.Aglib.FieldTheory.RatFuncInversion, `Motivic.Aglib.FieldTheory.RatFuncReverse]
  let consumerPrefix := `AglibTest.MilnorK3PolynomialNorm
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
        throwError "Polynomial norm declaration {name} is absent from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃, polynomial local residue, rational inversion/reversal, \
    and polynomial norm declarations, including private helpers: \
    only standard Lean logical foundations."
