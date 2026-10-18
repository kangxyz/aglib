/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.PolynomialNormProjection
import Lean.Util.CollectAxioms

/-!
# Original-group mixed projection consumers and rejecting axiom audit

The arbitrary input unit is quantified in the literal quotient field. The norm
on the right is the ordinary determinant norm, and the group on each side is
the original integer tensor/Steinberg Milnor K₂ quotient.
-/

open Polynomial
open MilnorK.K2 MilnorK.K3
open MilnorK.K3.PolynomialResidue
open MilnorK.K3.PolynomialNorm

noncomputable section

namespace AglibTest.MilnorK3PolynomialNormProjection

variable {k : Type*} [Field k]

/-- The source is the original tensor/Steinberg quotient over the actual root algebra. -/
theorem actual_original_source (p : MonicIrreducible k) :
    MilnorK.K2.Group (AdjoinRoot p.val) =
      (TensorProduct ℤ (Additive (AdjoinRoot p.val)ˣ) (Additive (AdjoinRoot p.val)ˣ) ⧸
        steinbergSpan (AdjoinRoot p.val)) := rfl

/-- The target is the original base-field integer tensor/Steinberg quotient. -/
theorem actual_original_target :
    MilnorK.K2.Group k = (TensorProduct ℤ (Additive kˣ) (Additive kˣ) ⧸ steinbergSpan k) := rfl

/-- Distinct irreducibles have exactly the two displayed actual finite residues. -/
theorem actual_two_place_residue [DecidableEq (MonicIrreducible k)]
    (p q : MonicIrreducible k) (hpq : p ≠ q) (b : kˣ) :
    totalResidue (symbol3 (polynomialUnit p.val p.property.2.ne_zero)
      (polynomialUnit q.val q.property.2.ne_zero) (InfinityResidue.constantUnit k b)) =
      DFinsupp.single p (symbol (quotientUnit p.val q.val (not_dvd_of_ne q p hpq.symm))
        (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) -
      DFinsupp.single q (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq))
        (Units.map (algebraMap k (AdjoinRoot q.val)).toMonoidHom b)) :=
  totalResidue_polynomials_constant p q hpq b

/-- The infinity term keeps both degrees and the sign in every characteristic. -/
theorem actual_infinity_sign (p q : k[X]) (hp : p.Monic) (hq : q.Monic) (b : kˣ) :
    InfinityResidue.residue k (symbol3 (polynomialUnit p hp.ne_zero)
      (polynomialUnit q hq.ne_zero) (InfinityResidue.constantUnit k b)) =
      (p.natDegree * q.natDegree) • symbol (-1) b :=
  residue_polynomials_constant p q hp hq b

/-- Both finite norm terms and the infinity sign are computed by the actual maps. -/
theorem actual_two_place_norm_reciprocity (p q : MonicIrreducible k)
    (hpq : p ≠ q) (b : kˣ) :
    polynomialNorm p (symbol (quotientUnit p.val q.val (not_dvd_of_ne q p hpq.symm))
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      polynomialNorm q (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq))
        (Units.map (algebraMap k (AdjoinRoot q.val)).toMonoidHom b)) +
      (p.val.natDegree * q.val.natDegree) • symbol (-1) b :=
  polynomialNorm_polynomial_reciprocity p q hpq b

/-- The first entry ranges over all original residue-field units. -/
theorem arbitrary_mixed_projection [CharZero k] (p : MonicIrreducible k)
    (a : (AdjoinRoot p.val)ˣ) (b : kˣ) :
    polynomialNorm p (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      symbol (Units.map (Algebra.norm k) a) b :=
  polynomialNorm_symbol_constant p a b

/-- The same original-group formula holds with the scalar in the first entry. -/
theorem arbitrary_reversed_mixed_projection [CharZero k] (p : MonicIrreducible k)
    (a : kˣ) (b : (AdjoinRoot p.val)ˣ) :
    polynomialNorm p (symbol
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom a) b) =
      symbol a (Units.map (Algebra.norm k) b) :=
  polynomialNorm_constant_symbol p a b

/-- Representatives may have arbitrary degree and need not be roots or irreducibles. -/
theorem arbitrary_polynomial_projection [CharZero k] (p : MonicIrreducible k)
    (A : k[X]) (hA : ¬ p.val ∣ A) (b : kˣ) :
    polynomialNorm p (symbol (quotientUnit p.val A hA)
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      symbol (Units.map (Algebra.norm k) (quotientUnit p.val A hA)) b :=
  polynomialNorm_symbol_constant p (quotientUnit p.val A hA) b

/-- Products of arbitrary original units are handled by their actual determinant norms. -/
theorem arbitrary_product_projection [CharZero k] (p : MonicIrreducible k)
    (a c : (AdjoinRoot p.val)ˣ) (b : kˣ) :
    polynomialNorm p (symbol (a * c)
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      symbol (Units.map (Algebra.norm k) a) b + symbol (Units.map (Algebra.norm k) c) b := by
  rw [polynomialNorm_symbol_constant, map_mul, symbol_mul_left]

end AglibTest.MilnorK3PolynomialNormProjection

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.RingTheory.AdjoinRootNormEvaluation,
    `Aglib.RingTheory.AdjoinRootNormResultant,
    `Aglib.RingTheory.AdjoinRootNormRoot,
    `Aglib.RingTheory.PolynomialLocalResidue]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "The polynomial norm projection audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue,
    `Motivic.Aglib.FieldTheory.RatFuncInversion, `Motivic.Aglib.FieldTheory.RatFuncReverse,
    `Motivic.Aglib.RingTheory.AdjoinRootNormEvaluation,
    `Motivic.Aglib.RingTheory.AdjoinRootNormRoot,
    `Motivic.Aglib.RingTheory.AdjoinRootNormResultant]
  let consumerPrefix := `AglibTest.MilnorK3PolynomialNormProjection
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
        throwError "Polynomial norm projection declaration {name} is absent \
          from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} original Milnor K₂/K₃, polynomial local residue, \
    determinant norm/resultant, rational inversion/reversal, and mixed projection \
    consumer declarations, including private helpers: only standard Lean logical foundations."
