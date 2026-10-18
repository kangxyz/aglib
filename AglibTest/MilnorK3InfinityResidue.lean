/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.InfinityResidue
import Lean.Util.CollectAxioms

/-!
# Actual infinity residue consumers and rejecting axiom audit

The consumers retain the original tensor quotients, concrete rational-function
substitution, and literal units. They test entire constant classes as well as
both uniformizer signs. The legacy import admits all private implementation
helpers to the rejecting transitive axiom audit.
-/

open Polynomial
open MilnorK.K2 MilnorK.K3
open MilnorK.K3.InfinityResidue

noncomputable section

namespace AglibTest.MilnorK3InfinityResidue

variable {k : Type*} [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- The source is the original nested tensor/Steinberg quotient. -/
theorem actual_source :
    MilnorK.K3.Group (RatFunc k) = (TensorProduct ℤ (Additive (RatFunc k)ˣ) (MilnorK.K2.Group (RatFunc k)) ⧸
      R3 (RatFunc k)) := rfl

/-- The target is the literal original Milnor K₂ quotient over the base field. -/
theorem actual_original_target :
    MilnorK.K2.Group k = (TensorProduct ℤ (Additive kˣ) (Additive kˣ) ⧸ steinbergSpan k) := rfl

/-- The whole map is finite residue after the actual inversion automorphism. -/
theorem actual_composition :
    residue k =
      (MilnorK.K2.map (rootXEquiv k).toRingHom).comp
        ((PolynomialResidue.residueAt (X : k[X])).comp
          (MilnorK.K3.map (RatFunc.inversion k).toRingHom)) := rfl

/-- The rational-function automorphism substitutes in actual polynomial fractions. -/
theorem actual_fraction_substitution (p q : k[X]) :
    RatFunc.inversion k (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q) =
      aeval (RatFunc.X⁻¹ : RatFunc k) p / aeval (RatFunc.X⁻¹ : RatFunc k) q := by
  change RatFunc.inversionHom k (_ / _) = _
  simp only [map_div₀, RatFunc.inversionHom_algebraMap]

/-- The concrete substitution is involutive on arbitrary rational functions. -/
theorem actual_inversion_involutive (f : RatFunc k) :
    RatFunc.inversion k (RatFunc.inversion k f) = f := RatFunc.inversion_inversion k f

/-- The residue-field identification is literal evaluation at zero. -/
theorem actual_residue_field_evaluation (q : k[X]) :
    rootXEquiv k (AdjoinRoot.mk (X : k[X]) q) = q.eval 0 := rootXEquiv_mk k q

/-- Field maps act on all three actual units, through the nested quotient. -/
theorem actual_field_map {l : Type*} [Field l] (f : k →+* l) (a b c : kˣ) :
    MilnorK.K3.map f (symbol3 a b c) =
      symbol3 (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b)
        (Units.map f.toMonoidHom c) := map_symbol3 f a b c

/-- The identity field map acts identically on complete K₃ classes. -/
theorem actual_field_map_identity (x : MilnorK.K3.Group k) :
    MilnorK.K3.map (RingHom.id k) x = x :=
  LinearMap.congr_fun MilnorK.K3.map_id x

/-- Composition holds on complete K₃ classes. -/
theorem actual_field_map_composition {l m : Type*} [Field l] [Field m]
    (f : k →+* l) (g : l →+* m) (x : MilnorK.K3.Group k) :
    MilnorK.K3.map (g.comp f) x =
      MilnorK.K3.map g (MilnorK.K3.map f x) :=
  LinearMap.congr_fun (MilnorK.K3.map_comp f g) x

/-- Every constant K₃ class has zero actual infinity residue. -/
theorem all_constant_classes (x : MilnorK.K3.Group k) :
    residue k (MilnorK.K3.map (algebraMap k (RatFunc k)) x) = 0 :=
  residue_constants k x

/-- The inverse variable is the positive infinity uniformizer, with literal entries. -/
theorem inverse_variable_literal_normalization (a b : kˣ) :
    residue k
      (symbol3 (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)⁻¹
        (Units.map (algebraMap k (RatFunc k)).toMonoidHom a)
        (Units.map (algebraMap k (RatFunc k)).toMonoidHom b)) = symbol a b :=
  residue_inv_variable k a b

/-- The variable has negative infinity residue, with the sign retained. -/
theorem variable_literal_normalization (a b : kˣ) :
    residue k
      (symbol3 (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
        (Units.map (algebraMap k (RatFunc k)).toMonoidHom a)
        (Units.map (algebraMap k (RatFunc k)).toMonoidHom b)) = -symbol a b :=
  residue_variable k a b

/-- Three literal constant units vanish under the constructed residue. -/
theorem literal_constant_symbols (a b c : kˣ) :
    residue k
      (symbol3 (Units.map (algebraMap k (RatFunc k)).toMonoidHom a)
        (Units.map (algebraMap k (RatFunc k)).toMonoidHom b)
        (Units.map (algebraMap k (RatFunc k)).toMonoidHom c)) = 0 :=
  residue_constant_symbols k a b c

end AglibTest.MilnorK3InfinityResidue

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
    throwError "The infinity Milnor residue audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue,
    `Motivic.Aglib.FieldTheory.RatFuncInversion]
  let consumerPrefix := `AglibTest.MilnorK3InfinityResidue
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
        throwError "Infinity Milnor residue declaration {name} is absent from \
          the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃, polynomial local residue, rational inversion, \
    and consumer declarations, including private helpers: only standard Lean logical foundations."
