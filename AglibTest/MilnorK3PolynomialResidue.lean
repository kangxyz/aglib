/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.PolynomialResidue
import Lean.Util.CollectAxioms

/-!
# Actual finite-polynomial residue consumers and rejecting axiom audit

These consumers expose the literal rational-function units, polynomial quotient
units, and the actual localization at `(p)`. The residue is the original K₂
field map after the constructed, uniformizer-independent DVR residue. MotivicTest
retain arbitrary base fields and do not assume separability or a norm theorem.
Legacy imports expose private implementation helpers for the complete audit.
-/

open Polynomial
open MilnorK.K2 MilnorK.K3
open MilnorK.K3.PolynomialResidue

noncomputable section

namespace AglibTest.MilnorK3PolynomialResidue

variable {k : Type*} [Field k] (p : k[X]) [Fact (Irreducible p)]

/-- The source is the actual nested tensor/Steinberg quotient of rational functions. -/
theorem actual_source :
    MilnorK.K3.Group (RatFunc k) = (TensorProduct ℤ (Additive (RatFunc k)ˣ) (MilnorK.K2.Group (RatFunc k)) ⧸
      R3 (RatFunc k)) := rfl

/-- The target remains the original Milnor K₂ tensor/Steinberg quotient. -/
theorem actual_original_target :
    MilnorK.K2.Group (AdjoinRoot p) =
      (TensorProduct ℤ (Additive (AdjoinRoot p)ˣ) (Additive (AdjoinRoot p)ˣ) ⧸
        steinbergSpan (AdjoinRoot p)) := rfl

/-- The complete residue map is the literal composition on the actual polynomial local ring. -/
theorem actual_composition :
    residueAt p =
      (MilnorK.K2.map (LocalResidue.residueEquiv p).toRingHom).comp
        (MilnorK.K3.DVR.residue
          (Localization.AtPrime (Ideal.span {p})) (RatFunc k)) := rfl

/-- This equality applies to arbitrary classes, rather than only chosen polynomial symbols. -/
theorem actual_composition_apply (x : MilnorK.K3.Group (RatFunc k)) :
    residueAt p x =
      MilnorK.K2.map (LocalResidue.residueEquiv p).toRingHom
        (MilnorK.K3.DVR.residue
          (Localization.AtPrime (Ideal.span {p})) (RatFunc k) x) := rfl

/-- Every actual local uniformizer computes the same finite-polynomial residue map. -/
theorem every_actual_uniformizer {π : LocalResidue.Ring p} (hπ : Irreducible π) :
    residueAt p =
      (MilnorK.K2.map (LocalResidue.residueEquiv p).toRingHom).comp
        (MilnorK.K3.DVR.residueWithUniformizer (K := RatFunc k) hπ) := by
  rw [residueAt, MilnorK.K3.DVR.residue_eq hπ]

/-- The local-unit witness has precisely the given polynomial as its value. -/
theorem actual_local_unit (q : k[X]) (hq : ¬ p ∣ q) :
    (localUnit p q hq : Localization.AtPrime (Ideal.span {p})) =
      algebraMap k[X] (Localization.AtPrime (Ideal.span {p})) q :=
  localUnit_coe p q hq

/-- Actual quotient units also agree with evaluation at the original adjoined root. -/
theorem actual_evaluation_class (q : k[X]) (hq : ¬ p ∣ q) :
    (quotientUnit p q hq : AdjoinRoot p) = aeval (AdjoinRoot.root p) q := by
  rw [quotientUnit_coe, AdjoinRoot.aeval_eq]

/-- Normalization is about literal units of the input polynomials and quotient classes. -/
theorem normalization_literal_units (hp : p.Monic) (q r : k[X])
    (hq : q ≠ 0) (hr : r ≠ 0)
    (hqdeg : q.natDegree < p.natDegree) (hrdeg : r.natDegree < p.natDegree) :
    residueAt p
      (symbol3
        (Units.mk0 (algebraMap k[X] (RatFunc k) p)
          (RatFunc.algebraMap_ne_zero (Fact.out : Irreducible p).ne_zero))
        (Units.mk0 (algebraMap k[X] (RatFunc k) q) (RatFunc.algebraMap_ne_zero hq))
        (Units.mk0 (algebraMap k[X] (RatFunc k) r) (RatFunc.algebraMap_ne_zero hr))) =
      symbol
        (Units.mk0 (AdjoinRoot.mk p q) (AdjoinRoot.mk_ne_zero_of_natDegree_lt hp hq hqdeg))
        (Units.mk0 (AdjoinRoot.mk p r) (AdjoinRoot.mk_ne_zero_of_natDegree_lt hp hr hrdeg)) :=
  residueAt_reduced p hp q r hq hr hqdeg hrdeg

/-- Coprime polynomial entries have zero residue, stated with literal rational-function units. -/
theorem coprime_literal_units (a b c : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hap : IsCoprime p a) (hbp : IsCoprime p b) (hcp : IsCoprime p c) :
    residueAt p
      (symbol3
        (Units.mk0 (algebraMap k[X] (RatFunc k) a) (RatFunc.algebraMap_ne_zero ha))
        (Units.mk0 (algebraMap k[X] (RatFunc k) b) (RatFunc.algebraMap_ne_zero hb))
        (Units.mk0 (algebraMap k[X] (RatFunc k) c) (RatFunc.algebraMap_ne_zero hc))) = 0 :=
  residueAt_coprime p a b c ha hb hc hap hbp hcp

end AglibTest.MilnorK3PolynomialResidue

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
    throwError "The polynomial Milnor residue audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue]
  let consumerPrefix := `AglibTest.MilnorK3PolynomialResidue
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
        throwError "Polynomial Milnor residue declaration {name} is absent from \
          the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃, polynomial local residue, and consumer declarations, \
    including private helpers: only standard Lean logical foundations."
