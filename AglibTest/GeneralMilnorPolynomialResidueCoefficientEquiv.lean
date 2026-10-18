/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Polynomial.CoefficientEquiv
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Direct consumers of actual rational coefficient equivalences and exact
all-class residue transport, without norm compatibility assumptions. -/

open Polynomial Polynomial.LocalResidue
open MilnorK
open scoped RatFunc

attribute [local instance] Polynomial.algebra

namespace AglibTest.GeneralMilnorPolynomialResidueCoefficientEquiv

variable {A B : Type*} [Field A] [Field B]

/-- Both directions are the original coefficient maps, not merely unspecified
field isomorphisms satisfying a compatibility assumption. -/
theorem actual_forward_and_inverse (φ : A ≃+* B) :
    (fractionMapRingEquiv φ).toRingHom = fractionMap φ.toRingHom ∧
      (fractionMapRingEquiv φ).symm.toRingHom = fractionMap φ.symm.toRingHom :=
  ⟨rfl, rfl⟩

/-- Algebra transport uses the native rational-function base field. -/
theorem actual_rational_base {k : Type*} [Field k] [Algebra k A] [Algebra k B]
    (φ : A ≃ₐ[k] B) (x : RatFunc k) :
    fractionMap φ.toRingHom (algebraMap (RatFunc k) (RatFunc A) x) =
      algebraMap (RatFunc k) (RatFunc B) x :=
  (fractionMapAlgEquiv φ).commutes x

/-- Restriction to the original base field retains exactly the same field map. -/
theorem actual_original_base {k : Type*} [Field k] [Algebra k A] [Algebra k B]
    (φ : A ≃ₐ[k] B) :
    ((fractionMapAlgEquiv φ).restrictScalars k).toRingHom = fractionMap φ.toRingHom := rfl

section FinitePlace

variable (φ : A ≃+* B) (p : A[X]) [Fact (Irreducible p)]

local instance : Fact (Irreducible (p.map φ.toRingHom)) :=
  ⟨irreducible_map_ringEquiv φ p Fact.out⟩

/-- Arbitrary irreducible places and arbitrary quotient classes are allowed;
no separability, monicity, or characteristic-zero premise is present. -/
theorem original_mapped_place (n : ℕ) (x : K (RatFunc A) (n + 1)) :
    PolynomialResidue.residueAt (p.map φ.toRingHom) n
        (map (n + 1) (fractionMap φ.toRingHom) x) =
      map n
        (AdjoinRoot.mapRingEquiv φ p (p.map φ.toRingHom) (Associated.refl _)).toRingHom
        (PolynomialResidue.residueAt p n x) :=
  PolynomialResidue.residueAt_mapRingEquiv φ p n x

end FinitePlace

local instance : Fact (Irreducible (X : A[X])) := ⟨irreducible_X⟩
local instance : Fact (Irreducible (X : B[X])) := ⟨irreducible_X⟩

/-- The coefficient-normalized finite residue also works over the original
field maps, hence can be inserted directly into an actual norm square. -/
theorem normalized_original_place (φ : A ≃+* B) (n : ℕ)
    (x : K (RatFunc A) (n + 1)) :
    map n (InfinityResidue.rootXEquiv B).toRingHom
        (PolynomialResidue.residueAt (X : B[X]) n
          (map (n + 1) (fractionMapRingEquiv φ).toRingHom x)) =
      map n φ.toRingHom
        (map n (InfinityResidue.rootXEquiv A).toRingHom
          (PolynomialResidue.residueAt (X : A[X]) n x)) :=
  PolynomialResidue.residueAt_X_restrict_normalized φ.toRingHom n x

local instance : Fact (Irreducible (X : (ZMod 2)[X])) := ⟨irreducible_X⟩

/-- The exact normalized square admits a concrete positive-characteristic
source field as well as every degree and every Milnor class. -/
theorem normalized_characteristic_two (ψ : ZMod 2 →+* B) (n : ℕ)
    (x : K (RatFunc (ZMod 2)) (n + 1)) :
    map n (InfinityResidue.rootXEquiv B).toRingHom
        (PolynomialResidue.residueAt (X : B[X]) n (map (n + 1) (fractionMap ψ) x)) =
      map n ψ
        (map n (InfinityResidue.rootXEquiv (ZMod 2)).toRingHom
          (PolynomialResidue.residueAt (X : (ZMod 2)[X]) n x)) :=
  PolynomialResidue.residueAt_X_restrict_normalized ψ n x

end AglibTest.GeneralMilnorPolynomialResidueCoefficientEquiv

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncCoefficientEquiv,
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RationalCoefficientRoot,
    `Aglib.RingTheory.AdjoinRootCoefficientEquiv,
    `Aglib.RingTheory.PolynomialLocalResidue,
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
  let prefixes := #[`Polynomial.LocalResidue, `MilnorK,
    `AglibTest.GeneralMilnorPolynomialResidueCoefficientEquiv]
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
  logInfo m!"Checked {names.size} actual rational coefficient and Milnor residue declarations: \
    standard axioms only."
