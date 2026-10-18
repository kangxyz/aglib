/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.PrimeInduction
import Lean.Util.CollectAxioms

/-! Consumers for the nonnormal prime induction step. Every occurrence of the
smaller-degree presentation-independence hypothesis remains visible. -/

open Polynomial
open MilnorK MilnorK.PolynomialResidue
open MilnorK.PolynomialNorm

namespace AglibTest.GeneralMilnorPolynomialNormPrimeInduction

variable {k : Type*} [Field k] [CharZero k]

/-- The root-field induction hypothesis gives an actual annihilator over k,
without assuming the original extension is normal. -/
theorem actual_degree_annihilator (n : ℕ) (p q : MonicIrreducible k)
    (hp : 1 < p.val.natDegree) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (ih : ∀ (r s : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < p.val.natDegree →
      ∀ (ε : AdjoinRoot r.val ≃ₐ[AdjoinRoot p.val] AdjoinRoot s.val)
        (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (map n ε.toRingHom y) = polynomialNorm n r y)
    (x : K (AdjoinRoot p.val) n) :
    (p.val.natDegree : ℤ) •
      (polynomialNorm n q (map n e.toRingHom x) - polynomialNorm n p x) = 0 :=
  polynomialNorm_degree_smul_sub_eq_zero_of_lower_degrees n p q hp e ih x

/-- Combining the proven annihilator with a finite coprime mixed restriction
closes the prime step for arbitrary classes, not only individual symbols. -/
theorem nonnormal_prime_step (n : ℕ) (p q : MonicIrreducible k)
    (hp : p.val.natDegree.Prime) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (ih : ∀ (r s : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < p.val.natDegree →
      ∀ (ε : AdjoinRoot r.val ≃ₐ[AdjoinRoot p.val] AdjoinRoot s.val)
        (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (map n ε.toRingHom y) = polynomialNorm n r y)
    (x : K (AdjoinRoot p.val) n) :
    polynomialNorm n q (map n e.toRingHom x) = polynomialNorm n p x :=
  polynomialNorm_map_algEquiv_of_prime_of_lower_degrees n p q hp e ih x

end AglibTest.GeneralMilnorPolynomialNormPrimeInduction

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.CoprimeIrreducibility,
    `Aglib.FieldTheory.FiniteCoprimeSplitting,
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.FieldTheory.SylowFixedField,
    `Aglib.RingTheory.AdjoinRootCoefficientEquiv,
    `Aglib.RingTheory.AdjoinRootScalarBranches,
    `Aglib.RingTheory.PolynomialLocalResidue,
    `Aglib.RingTheory.PolynomialPlaceContraction,
    `Aglib.RingTheory.PolynomialResidueBaseChange]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`MilnorK,
    `AglibTest.GeneralMilnorPolynomialNormPrimeInduction]
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
  logInfo m!"Checked {names.size} prime induction and Milnor declarations: \
    standard axioms only."
