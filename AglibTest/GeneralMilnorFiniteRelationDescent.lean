/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.FiniteRelationDescent
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Actual finite-relation consumers on the original Milnor presentation and
quotients. Algebraic descent is tested without separability; prime-to-order
detection retains it. Legacy imports expose all checked proof bodies. -/

open MilnorK MilnorK.FiniteDescent

namespace AglibTest.GeneralMilnorFiniteRelationDescent

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

section Algebraic

variable [Algebra.IsAlgebraic k E]

omit [Algebra.IsAlgebraic k E] in
/-- The actual free presentation map is injective, independently of quotient kernels. -/
theorem free_presentation_injective (n : ℕ) :
    Function.Injective (presentationMap n (algebraMap k E)) :=
  presentationMap_injective n (algebraMap k E)

/-- The descended witness belongs to the genuine defining relation submodule. -/
theorem actual_relation_witness (n : ℕ) (r : Presentation E n)
    (hr : r ∈ relationSpan E n) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ s : Presentation S n, s ∈ relationSpan S n ∧
        presentationMap n S.val.toRingHom s = r :=
  exists_finite_relation k E n r hr

/-- Arbitrary class vanishing descends with no separability assumption. -/
theorem actual_finite_vanishing (n : ℕ) (x : K k n)
    (hx : map n (algebraMap k E) x = 0) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      map n (algebraMap k S) x = 0 :=
  exists_finite_intermediate_map_eq_zero k E n x hx

/-- The zero-degree quotient is included. -/
theorem empty_tuple_vanishing (x : K k 0) (hx : map 0 (algebraMap k E) x = 0) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      map 0 (algebraMap k S) x = 0 :=
  exists_finite_intermediate_map_eq_zero k E 0 x hx

/-- Equality, as well as vanishing, has a finite witness. -/
theorem actual_finite_equality (n : ℕ) (x y : K k n)
    (hxy : map n (algebraMap k E) x = map n (algebraMap k E) y) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      map n (algebraMap k S) x = map n (algebraMap k S) y :=
  exists_finite_intermediate_map_eq k E n x y hxy

/-- The finite witness also works on the original degree-two Steinberg quotient. -/
theorem original_degree_two (x : MilnorK.K2.Group k)
    (hx : MilnorK.K2.map (algebraMap k E) x = 0) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      MilnorK.K2.map (algebraMap k S) x = 0 := by
  have hx' : map 2 (algebraMap k E) ((twoEquiv k).symm x) = 0 := by
    apply (twoEquiv E).injective
    rw [twoEquiv_map, LinearEquiv.apply_symm_apply, hx, map_zero]
  obtain ⟨S, hS, h⟩ := exists_finite_intermediate_map_eq_zero k E 2
    ((twoEquiv k).symm x) hx'
  refine ⟨S, hS, ?_⟩
  simpa only [twoEquiv_map, LinearEquiv.apply_symm_apply, map_zero] using
    congrArg (twoEquiv S) h

end Algebraic

omit [Algebra k E] in
/-- A literal field map may supply the algebraic extension structure. -/
theorem actual_field_map (φ : k →+* E)
    (hAlg : letI := φ.toAlgebra; Algebra.IsAlgebraic k E) (n : ℕ) (x : K k n)
    (hx : map n φ x = 0) :
    letI := φ.toAlgebra
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      map n (algebraMap k S) x = 0 := by
  let := φ.toAlgebra
  let := hAlg
  exact exists_finite_intermediate_map_eq_zero k E n x hx

/-- Positive-characteristic algebraic extensions need not be declared separable. -/
theorem characteristic_two [Algebra (ZMod 2) E] [Algebra.IsAlgebraic (ZMod 2) E]
    (n : ℕ) (x : K (ZMod 2) n) (hx : map n (algebraMap (ZMod 2) E) x = 0) :
    ∃ S : IntermediateField (ZMod 2) E, FiniteDimensional (ZMod 2) S ∧
      map n (algebraMap (ZMod 2) S) x = 0 :=
  exists_finite_intermediate_map_eq_zero (ZMod 2) E n x hx

section Separable

variable [Algebra.IsSeparable k E]

/-- Torsion detection keeps all actual finite-degree hypotheses explicit. -/
theorem coprime_detection (n m : ℕ)
    (hdeg : ∀ S : IntermediateField k E, FiniteDimensional k S →
      m.Coprime (Module.finrank k S))
    (x : K k n) (hx : map n (algebraMap k E) x = 0) (hxm : (m : ℤ) • x = 0) : x = 0 :=
  eq_zero_of_map_eq_zero_of_finite_degrees_coprime k E n m hdeg x hx hxm

/-- The prime-power torsion consequence uses no asserted special closure. -/
theorem primary_detection (n p r : ℕ)
    (hdeg : ∀ S : IntermediateField k E, FiniteDimensional k S →
      p.Coprime (Module.finrank k S))
    (x : K k n) (hx : map n (algebraMap k E) x = 0)
    (hxp : ((p ^ r : ℕ) : ℤ) • x = 0) : x = 0 :=
  eq_zero_of_map_eq_zero_of_finite_degrees_coprime_pow k E n p r hdeg x hx hxp

end Separable

end AglibTest.GeneralMilnorFiniteRelationDescent

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
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorFiniteRelationDescent]
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
  logInfo m!"Checked {names.size} finite relation descent and general Milnor declarations: \
    standard axioms only."
