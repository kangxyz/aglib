/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.FiniteComparison
import Aglib.KTheory.MilnorK.RestrictionKernel
import Lean.Util.CollectAxioms

/-! Actual mixed, singleton-factor, finite restriction, and coprime-torsion
consumers. The last consumer states its torsion premise explicitly; it does
not assert that arbitrary prime-degree extensions are normal. -/

open Polynomial Polynomial.LocalResidue
open MilnorK MilnorK.PolynomialResidue MilnorK.PolynomialNorm

namespace AglibTest.GeneralMilnorPolynomialNormFiniteComparison

variable {k L : Type*} [Field k] [Field L]

/-- The mixed-span comparison has no generation premise for the entire field. -/
theorem actual_mixed_comparison [CharZero k] (m : ℕ) (p q : MonicIrreducible k)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) (x : K (AdjoinRoot p.val) (m + 1))
    (hx : x ∈ mixedSpan (algebraMap k (AdjoinRoot p.val)) m) :
    polynomialNorm (m + 1) q (map (m + 1) e.toRingHom x) = polynomialNorm (m + 1) p x :=
  polynomialNorm_map_algEquiv_of_mem_mixedSpan m p q e x hx

/-- Actual root-algebra equivalence forces the equality of presentation degrees. -/
theorem actual_degree (p q : MonicIrreducible k)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) : p.val.natDegree = q.val.natDegree :=
  natDegree_eq_of_root_algEquiv p q e

/-- The source has exactly one target factor when the whole image is irreducible. -/
theorem actual_singleton (φ : k →+* L) (p : MonicIrreducible k)
    (q : MonicIrreducible L) (hq : q.val = p.val.map φ) : placesAbove φ p = {q} :=
  placesAbove_eq_singleton φ p q hq

/-- Singleton-factor coefficient base change is valid also in Milnor degree zero. -/
theorem actual_degree_zero [CharZero k] (φ : k →+* L)
    (p : MonicIrreducible k) (q : MonicIrreducible L) (hq : q.val = p.val.map φ)
    (z : K (AdjoinRoot p.val) 0) :
    map 0 φ (polynomialNorm 0 p z) =
      polynomialNorm 0 q (map 0 (adjoinRootMap φ p.val q.val (hq ▸ dvd_rfl)) z) :=
  polynomialNorm_restrict_irreducible φ 0 p q hq z

universe u

/-- The result supplies a genuine finite extension and equality of the two
restricted values on an arbitrary original class. Normality is not assumed. -/
theorem actual_finite_restriction {k : Type u} [Field k] [CharZero k]
    (p q : MonicIrreducible k) (hp : p.val.natDegree.Prime)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (m : ℕ) (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      p.val.natDegree.Coprime (Module.finrank k L) ∧
      map (m + 1) (algebraMap k L)
          (polynomialNorm (m + 1) q (map (m + 1) e.toRingHom x)) =
        map (m + 1) (algebraMap k L) (polynomialNorm (m + 1) p x) :=
  exists_coprime_restriction_eq_of_algEquiv p q hp e m x

/-- The literal empty prefix includes ordinary degree-one classes. -/
theorem empty_prefix {k : Type u} [Field k] [CharZero k]
    (p q : MonicIrreducible k) (hp : p.val.natDegree.Prime)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) (x : K (AdjoinRoot p.val) 1) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      p.val.natDegree.Coprime (Module.finrank k L) ∧
      map 1 (algebraMap k L) (polynomialNorm 1 q (map 1 e.toRingHom x)) =
        map 1 (algebraMap k L) (polynomialNorm 1 p x) :=
  exists_coprime_restriction_eq_of_algEquiv p q hp e 0 x

/-- If an independent argument supplies prime-power annihilation of the
norm difference, the proved finite restriction comparison detects equality. -/
theorem equality_of_explicit_prime_power_torsion {k : Type u} [Field k] [CharZero k]
    (p q : MonicIrreducible k) (hp : p.val.natDegree.Prime)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (m r : ℕ) (x : K (AdjoinRoot p.val) (m + 1))
    (htors : ((p.val.natDegree ^ r : ℕ) : ℤ) •
      (polynomialNorm (m + 1) q (map (m + 1) e.toRingHom x) - polynomialNorm (m + 1) p x) = 0) :
    polynomialNorm (m + 1) q (map (m + 1) e.toRingHom x) = polynomialNorm (m + 1) p x := by
  obtain ⟨L, hL, hA, hfd, hsep, hcop, heq⟩ :=
    exists_coprime_restriction_eq_of_algEquiv p q hp e m x
  let := hfd
  let := hsep
  apply sub_eq_zero.mp
  exact eq_zero_of_map_eq_zero_of_coprime_pow k L (m + 1) p.val.natDegree r hcop _
    (by rw [map_sub, heq, sub_self]) htors

end AglibTest.GeneralMilnorPolynomialNormFiniteComparison

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
    `AglibTest.GeneralMilnorPolynomialNormFiniteComparison]
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
  logInfo m!"Checked {names.size} finite norm-comparison and general Milnor declarations: \
    standard axioms only."
