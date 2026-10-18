/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalInversion
import Lean.Util.CollectAxioms

/-! Direct all-degree consumers of the actual rational inversion norm square. -/

open Polynomial Polynomial.LocalResidue
open MilnorK MilnorK.PolynomialResidue
open MilnorK.PolynomialNorm

namespace AglibTest.GeneralMilnorPolynomialNormRationalInversion

variable {k : Type*} [Field k] [CharZero k]
  (p : MonicIrreducible (RatFunc k))
  (hp : p.val.map (RatFunc.inversion k).toRingHom = p.val)

/-- An arbitrary class, including degree zero, uses the literal upper map. -/
theorem arbitrary_class (n : ℕ) (x : K (AdjoinRoot p.val) n) :
    map n (RatFunc.inversion k).toRingHom (polynomialNorm n p x) =
      polynomialNorm n p
        (map n (adjoinRootMap (RatFunc.inversion k).toRingHom p.val p.val
          (by rw [hp])) x) :=
  polynomialNorm_inversion p hp n x

/-- The existing degree-zero groups are also covered by the same square. -/
theorem empty_degree (x : K (AdjoinRoot p.val) 0) :
    map 0 (RatFunc.inversion k).toRingHom (polynomialNorm 0 p x) =
      polynomialNorm 0 p
        (map 0 (adjoinRootMap (RatFunc.inversion k).toRingHom p.val p.val
          (by rw [hp])) x) :=
  polynomialNorm_inversion p hp 0 x

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- The precise infinity-to-finite reduction does not assume a norm-residue law. -/
theorem actual_infinity_reduction (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    InfinityResidue.residue k n (polynomialNorm (n + 1) p x) =
      map n (InfinityResidue.rootXEquiv k).toRingHom
        (residueAt (X : k[X]) n
          (polynomialNorm (n + 1) p
            (map (n + 1) (adjoinRootMap (RatFunc.inversion k).toRingHom p.val p.val
              (by rw [hp])) x))) :=
  infinityResidue_polynomialNorm_eq_residueAt_X p hp n x

omit hp in
/-- A constant-coefficient presentation supplies fixedness rather than assuming it. -/
theorem constant_presentation (q : k[X]) (hq : p.val = q.map RatFunc.C)
    (n : ℕ) (x : K (AdjoinRoot p.val) n) :
    ∃ h : p.val.map (RatFunc.inversion k).toRingHom = p.val,
      map n (RatFunc.inversion k).toRingHom (polynomialNorm n p x) =
        polynomialNorm n p
          (map n (adjoinRootMap (RatFunc.inversion k).toRingHom p.val p.val
            (by rw [h])) x) := by
  have h : p.val.map (RatFunc.inversion k).toRingHom = p.val := by
    rw [hq]
    exact polynomial_map_inversion_map_C q
  exact ⟨h, polynomialNorm_inversion p h n x⟩

end AglibTest.GeneralMilnorPolynomialNormRationalInversion

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
    `AglibTest.GeneralMilnorPolynomialNormRationalInversion]
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
  logInfo m!"Checked {names.size} rational inversion and Milnor declarations: \
    standard axioms only."
