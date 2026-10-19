/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.DVRUniformizerBinomial
import Lean.Util.CollectAxioms

/-! Actual DVR binomial consumers include inseparable characteristic, exponent
one, and the even/odd determinant signs. No integral basis is supplied. -/

open Polynomial IsLocalRing

namespace AglibTest.DVRUniformizerBinomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
  {c : R} (hc : Irreducible c)

include hc

/-- Every positive exponent gives fraction-field irreducibility. -/
theorem actual_irreducible (e : ℕ) (he : 0 < e) :
    Irreducible (X ^ e - C (algebraMap R F c)) :=
  IsDiscreteValuationRing.uniformizer_binomial_irreducible_fraction F hc e he

/-- A characteristic-p exponent is included; no separability assumption occurs.
The explicitly unused instance fixes this regression's characteristic. -/
theorem inseparable_exponent (p : ℕ) (hp : Nat.Prime p) [_characteristicP : CharP F p] :
    Irreducible (X ^ p - C (algebraMap R F c)) :=
  actual_irreducible F hc p hp.pos

variable {E : Type*} [Field E] [Algebra F E]

/-- The literal root equation fixes the actual minimal polynomial. -/
theorem actual_minpoly (e : ℕ) (he : 0 < e) (θ : E)
    (hθ : θ ^ e = algebraMap F E (algebraMap R F c)) :
    minpoly F θ = X ^ e - C (algebraMap R F c) :=
  IsDiscreteValuationRing.minpoly_eq_uniformizer_binomial F hc e he θ hθ

variable [FiniteDimensional F E]

/-- Actual equal dimensions imply generation of the whole field. -/
theorem actual_primitive (e : ℕ) (he : 0 < e) (hd : Module.finrank F E = e)
    (θ : E) (hθ : θ ^ e = algebraMap F E (algebraMap R F c)) :
    IntermediateField.adjoin F {θ} = ⊤ :=
  IsDiscreteValuationRing.adjoin_uniformizer_binomial_root_eq_top F hc e he hd θ hθ

/-- The smallest exponent is genuinely allowed. -/
theorem degree_one (hd : Module.finrank F E = 1) (θ : E)
    (hθ : θ = algebraMap F E (algebraMap R F c)) :
    Algebra.norm F θ = algebraMap R F c := by
  simpa only [Nat.sub_self, pow_zero, one_mul] using
    IsDiscreteValuationRing.norm_uniformizer_binomial_root F hc 1 (by decide) hd θ
      (by simpa only [pow_one] using hθ)

/-- The quadratic determinant has the negative sign, even when it becomes
trivial in characteristic two. -/
theorem quadratic_sign (hd : Module.finrank F E = 2) (θ : E)
    (hθ : θ ^ 2 = algebraMap F E (algebraMap R F c)) :
    Algebra.norm F θ = -algebraMap R F c := by
  simpa using IsDiscreteValuationRing.norm_uniformizer_binomial_root F hc 2 (by decide) hd θ hθ

/-- The cubic determinant has the positive sign. -/
theorem cubic_sign (hd : Module.finrank F E = 3) (θ : E)
    (hθ : θ ^ 3 = algebraMap F E (algebraMap R F c)) :
    Algebra.norm F θ = algebraMap R F c := by
  simpa using IsDiscreteValuationRing.norm_uniformizer_binomial_root F hc 3 (by decide) hd θ hθ

end AglibTest.DVRUniformizerBinomial

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.RingTheory.DVRUniformizerBinomial]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let native := #[`IsDiscreteValuationRing.uniformizer_binomial_isEisensteinAt,
    `IsDiscreteValuationRing.uniformizer_binomial_irreducible,
    `IsDiscreteValuationRing.uniformizer_binomial_irreducible_fraction,
    `IsDiscreteValuationRing.minpoly_eq_uniformizer_binomial,
    `IsDiscreteValuationRing.adjoin_uniformizer_binomial_root_eq_top,
    `IsDiscreteValuationRing.norm_uniformizer_binomial_root]
  let selectedDeclaration (name : Name) := native.contains name ||
    (`AglibTest.DVRUniformizerBinomial).isPrefixOf name
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for name in native do names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} actual uniformizer-binomial declarations: standard axioms only."
