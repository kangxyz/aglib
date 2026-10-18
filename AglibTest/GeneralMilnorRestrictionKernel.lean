/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.RestrictionKernel
import Lean.Util.CollectAxioms

/-! Actual consumers of auxiliary degree retractions and finite separable
restriction kernels. The arbitrary-characteristic assumptions are retained.
Legacy imports expose checked proof bodies to the complete axiom audit. -/

open MilnorK

namespace AglibTest.GeneralMilnorRestrictionKernel

variable {k E L : Type*} [Field k] [Field E] [Field L]

section Algebra

variable [Algebra k E] [FiniteDimensional k E] [Algebra.IsSeparable k E]

/-- The existential map has the literal restriction composite in every degree. -/
theorem actual_degree_retraction (n : ℕ) :
    ∃ T : K E n →ₗ[ℤ] K k n,
      T.comp (map n (algebraMap k E)) = (Module.finrank k E : ℤ) • LinearMap.id := by
  obtain ⟨T, hT⟩ := exists_degree_retraction k E n
  exact ⟨T, LinearMap.ext hT⟩

/-- The empty-tuple degree is included. -/
theorem degree_zero_kernel (x : K k 0) (hx : map 0 (algebraMap k E) x = 0) :
    (Module.finrank k E : ℤ) • x = 0 :=
  finrank_smul_eq_zero_of_map_eq_zero k E 0 x hx

/-- Restricted torsion gives an actual product-of-degrees annihilator. -/
theorem restricted_torsion (n : ℕ) (m : ℤ) (x : K k n)
    (hx : m • map n (algebraMap k E) x = 0) :
    (m * (Module.finrank k E : ℤ)) • x = 0 :=
  mul_finrank_smul_eq_zero_of_smul_map_eq_zero k E n m x hx

/-- The general degree-two theorem recovers the original Steinberg quotient's
restriction-kernel annihilation using the genuine compatibility equivalence. -/
theorem original_degree_two (x : MilnorK.K2.Group k)
    (hx : MilnorK.K2.map (algebraMap k E) x = 0) :
    (Module.finrank k E : ℤ) • x = 0 := by
  have hmap : map 2 (algebraMap k E) ((twoEquiv k).symm x) = 0 := by
    apply (twoEquiv E).injective
    rw [twoEquiv_map, LinearEquiv.apply_symm_apply, hx, map_zero]
  have h := finrank_smul_eq_zero_of_map_eq_zero k E 2 ((twoEquiv k).symm x) hmap
  simpa only [map_smul, LinearEquiv.apply_symm_apply, map_zero] using
    congrArg (twoEquiv k) h

/-- Prime-to-`p` finite separable restriction detects actual `p`-primary torsion. -/
theorem primary_torsion_detection (n p r : ℕ)
    (hp : p.Coprime (Module.finrank k E)) (x : K k n)
    (hx : map n (algebraMap k E) x = 0) (hxp : ((p ^ r : ℕ) : ℤ) • x = 0) : x = 0 :=
  eq_zero_of_map_eq_zero_of_coprime_pow k E n p r hp x hx hxp

/-- Detection applies to differences, not only comparison to zero. -/
theorem compare_torsion_classes (n m : ℕ) (hm : m.Coprime (Module.finrank k E))
    (x y : K k n) (hxy : map n (algebraMap k E) x = map n (algebraMap k E) y)
    (hmxy : (m : ℤ) • (x - y) = 0) : x = y :=
  eq_of_map_eq_of_coprime k E n m hm x y hxy hmxy

end Algebra

/-- The actual field map supplies every algebra structure used by the statement. -/
theorem actual_field_map (φ : k →+* E)
    (hfin : letI := φ.toAlgebra; FiniteDimensional k E)
    (hsep : letI := φ.toAlgebra; Algebra.IsSeparable k E) (n : ℕ) (x : K k n)
    (hx : map n φ x = 0) :
    letI := φ.toAlgebra
    (Module.finrank k E : ℤ) • x = 0 :=
  finrank_smul_eq_zero_of_fieldMap_eq_zero k E φ hfin hsep n x hx

/-- No unrelated ambient algebra structure is used in the coprime-map theorem. -/
theorem actual_field_map_detection (φ : k →+* E)
    (hfin : letI := φ.toAlgebra; FiniteDimensional k E)
    (hsep : letI := φ.toAlgebra; Algebra.IsSeparable k E) (n m : ℕ)
    (hm : letI := φ.toAlgebra; m.Coprime (Module.finrank k E)) (x : K k n)
    (hx : map n φ x = 0) (hxm : (m : ℤ) • x = 0) : x = 0 :=
  eq_zero_of_fieldMap_eq_zero_of_coprime k E φ hfin hsep n m hm x hx hxm

/-- Two coprime extensions jointly detect all classes without an extension tower. -/
theorem joint_detection [Algebra k E] [Algebra k L]
    [FiniteDimensional k E] [FiniteDimensional k L]
    [Algebra.IsSeparable k E] [Algebra.IsSeparable k L]
    (hEL : (Module.finrank k E).Coprime (Module.finrank k L)) (n : ℕ) (x : K k n)
    (hE : map n (algebraMap k E) x = 0) (hL : map n (algebraMap k L) x = 0) : x = 0 :=
  eq_zero_of_two_maps_eq_zero_of_coprime k E L hEL n x hE hL

end AglibTest.GeneralMilnorRestrictionKernel

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
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorRestrictionKernel]
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
  logInfo m!"Checked {names.size} degree retraction/kernel and general Milnor declarations: \
    standard axioms only."
