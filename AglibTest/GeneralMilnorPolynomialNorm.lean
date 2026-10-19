/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.Basic
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-!
# Actual all-degree polynomial-norm consumers and rejecting axiom audit

The original Milnor groups, all actual finite places, and negative actual
infinity residue remain explicit. MotivicTest include arbitrary classes, the empty
tuple, characteristic two, lift independence, the positive degree law, and
left projection through actual field-to-valuation-ring maps.
No canonical norm for an abstract extension or tower law is assumed.
-/

noncomputable section

open Polynomial
open MilnorK MilnorK.PolynomialResidue MilnorK.PolynomialNorm

namespace AglibTest.GeneralMilnorPolynomialNorm

variable {F : Type*} [Field F]

/-- Source and target are the original all-degree Milnor presentations. -/
def originalPolynomialNorm (n : ℕ) (p : MonicIrreducible F) :
    K (AdjoinRoot p.val) n →ₗ[ℤ] K F n := polynomialNorm n p

/-- The actual quotient is by the constant image in degree `n+1`. -/
def actualConstantQuotientNorm (n : ℕ) :
    (K (RatFunc F) (n + 1) ⧸
      LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : F →+* RatFunc F))) →ₗ[ℤ] K F n :=
  quotientNorm n

/-- The total norm has the actual dependent finite residue sum as domain. -/
def originalTotalNorm (n : ℕ) :
    (Π₀ p : MonicIrreducible F, K (AdjoinRoot p.val) n) →ₗ[ℤ] K F n := totalNorm n

/-- Each representative computes the negative actual infinity residue. -/
theorem quotient_value (n : ℕ) (x : K (RatFunc F) (n + 1)) :
    quotientNorm n (Submodule.Quotient.mk x) = -InfinityResidue.residue F n x :=
  quotientNorm_mk n x

/-- Actual rational reciprocity holds for every original quotient class. -/
theorem actual_reciprocity (n : ℕ) (x : K (RatFunc F) (n + 1)) :
    totalNorm n (totalResidue n x) + InfinityResidue.residue F n x = 0 := by
  rw [totalNorm_totalResidue, neg_add_cancel]

/-- Any actual lift computes the same norm, without a prescribed representative. -/
theorem arbitrary_lift (n : ℕ)
    (y : Π₀ p : MonicIrreducible F, K (AdjoinRoot p.val) n)
    (x : K (RatFunc F) (n + 1)) (hx : totalResidue n x = y) :
    totalNorm n y = -InfinityResidue.residue F n x :=
  totalNorm_eq_neg_residue_of_lift n y x hx

/-- Infinity residues are independent of the lift chosen for a finite residue vector. -/
theorem actual_lift_independence (n : ℕ) (x y : K (RatFunc F) (n + 1))
    (h : totalResidue n x = totalResidue n y) :
    InfinityResidue.residue F n x = InfinityResidue.residue F n y :=
  infinity_residue_eq_of_totalResidue_eq n x y h

/-- The original residue relation uniquely characterizes the total norm. -/
theorem actual_uniqueness (n : ℕ)
    (f : (Π₀ p : MonicIrreducible F, K (AdjoinRoot p.val) n) →ₗ[ℤ] K F n)
    (hf : ∀ x : K (RatFunc F) (n + 1),
      f (totalResidue n x) = -InfinityResidue.residue F n x) :
    f = totalNorm n := totalNorm_unique n f hf

open scoped Classical in
/-- Every original single-place class has an actual rational-function lift. -/
theorem actual_single_place_lift (n : ℕ) (p : MonicIrreducible F)
    (y : K (AdjoinRoot p.val) n) :
    ∃ x : K (RatFunc F) (n + 1), totalResidue n x = DFinsupp.single p y ∧
      polynomialNorm n p y = -InfinityResidue.residue F n x := by
  obtain ⟨x, hx⟩ := totalResidue_surjective n (DFinsupp.single p y)
  exact ⟨x, hx, polynomialNorm_eq_neg_residue_of_lift n p y x hx⟩

open scoped Classical in
/-- The actual finite sum uses the genuine support of the actual residue vector. -/
theorem genuine_support_reciprocity (n : ℕ) (x : K (RatFunc F) (n + 1)) :
    (∑ p ∈ (totalResidue n x).support, polynomialNorm n p (residueAt p.val n x)) +
      InfinityResidue.residue F n x = 0 := finite_rational_reciprocity n x

/-- Restriction followed by the polynomial norm multiplies every class by degree. -/
theorem all_degree_constant_law (n : ℕ) (p : MonicIrreducible F) (x : K F n) :
    polynomialNorm n p (MilnorK.map n (algebraMap F (AdjoinRoot p.val)) x) =
      (p.val.natDegree : ℤ) • x := polynomialNorm_map_constants n p x

/-- Degree zero and its empty-symbol generator are included explicitly. -/
theorem empty_tuple_degree_law (p : MonicIrreducible F) :
    polynomialNorm 0 p
      (MilnorK.map 0 (algebraMap F (AdjoinRoot p.val)) (symbol Fin.elim0)) =
      (p.val.natDegree : ℤ) • symbol (F := F) Fin.elim0 :=
  polynomialNorm_map_constant_symbol 0 p Fin.elim0

/-- The construction and positive degree law include characteristic two. -/
theorem characteristic_two_degree_law (n : ℕ) (p : MonicIrreducible (ZMod 2))
    (x : K (ZMod 2) n) :
    polynomialNorm n p (MilnorK.map n (algebraMap (ZMod 2) (AdjoinRoot p.val)) x) =
      (p.val.natDegree : ℤ) • x := polynomialNorm_map_constants n p x

/-- Degree-one presentations act identically on the entire base-field image. -/
theorem degree_one_constants (n : ℕ) (p : MonicIrreducible F)
    (hp : p.val.natDegree = 1) (x : K F n) :
    polynomialNorm n p (MilnorK.map n (algebraMap F (AdjoinRoot p.val)) x) = x := by
  rw [polynomialNorm_map_constants, hp, Nat.cast_one, one_smul]

/-- Polynomial norms are integer-linear on arbitrary original residue-field classes. -/
theorem integer_linear (n : ℕ) (p : MonicIrreducible F) (a : ℤ)
    (x y : K (AdjoinRoot p.val) n) :
    polynomialNorm n p (a • x - y) = a • polynomialNorm n p x - polynomialNorm n p y := by
  rw [map_sub, map_smul]

/-- A base-field class acts through the actual finite DVR; the rational factor
is unrestricted, so its units may have poles and repeated uniformizers. -/
theorem actual_finite_projection (p : F[X]) [Fact (Irreducible p)] (m n : ℕ)
    (x : K F m) (z : K (RatFunc F) (n + 1)) :
    residueAt p (m + n)
      (product m (n + 1) (MilnorK.map m (RatFunc.C : F →+* RatFunc F) x) z) =
      product m n (MilnorK.map m (algebraMap F (AdjoinRoot p)) x) (residueAt p n z) :=
  residueAt_product_constants_left p m n x z

/-- The actual infinity map preserves left multiplication by every base-field class. -/
theorem actual_infinity_projection (m n : ℕ) (x : K F m)
    (z : K (RatFunc F) (n + 1)) :
    InfinityResidue.residue F (m + n)
      (product m (n + 1) (MilnorK.map m (RatFunc.C : F →+* RatFunc F) x) z) =
      product m n x (InfinityResidue.residue F n z) :=
  infinity_product_constants_left m n x z

/-- Arbitrary actual residue vectors satisfy the left projection formula. -/
theorem actual_total_projection (m n : ℕ) (x : K F m)
    (y : Π₀ p : MonicIrreducible F, K (AdjoinRoot p.val) n) :
    totalNorm (m + n) (residueProductLeft m n x y) = product m n x (totalNorm n y) :=
  totalNorm_product_constants_left m n x y

/-- Both factors of a polynomial norm's left projection formula are arbitrary
original quotient classes, with no simple-symbol hypothesis. -/
theorem actual_polynomial_projection (m n : ℕ) (p : MonicIrreducible F)
    (x : K F m) (y : K (AdjoinRoot p.val) n) :
    polynomialNorm (m + n) p
      (product m n (MilnorK.map m (algebraMap F (AdjoinRoot p.val)) x) y) =
      product m n x (polynomialNorm n p y) :=
  polynomialNorm_product_constants_left m n p x y

/-- Projection includes a degree-zero residue-field factor. -/
theorem degree_zero_right_projection (m : ℕ) (p : MonicIrreducible F)
    (x : K F m) (y : K (AdjoinRoot p.val) 0) :
    polynomialNorm (m + 0) p
      (product m 0 (MilnorK.map m (algebraMap F (AdjoinRoot p.val)) x) y) =
      product m 0 x (polynomialNorm 0 p y) :=
  polynomialNorm_product_constants_left m 0 p x y

/-- Left projection needs no odd-characteristic assumption. -/
theorem characteristic_two_projection (m n : ℕ) (p : MonicIrreducible (ZMod 2))
    (x : K (ZMod 2) m) (y : K (AdjoinRoot p.val) n) :
    polynomialNorm (m + n) p
      (product m n (MilnorK.map m (algebraMap (ZMod 2) (AdjoinRoot p.val)) x) y) =
      product m n x (polynomialNorm n p y) :=
  polynomialNorm_product_constants_left m n p x y

end AglibTest.GeneralMilnorPolynomialNorm

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
    throwError "The polynomial norm audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK, `MilnorK.K2,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue,
    `Motivic.Aglib.FieldTheory.RatFuncInversion, `Motivic.Aglib.FieldTheory.RatFuncReverse]
  let consumerPrefix := `AglibTest.GeneralMilnorPolynomialNorm
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
        throwError "General polynomial norm declaration {name} is absent \
          from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} general Milnor, polynomial local residue, \
    rational inversion/reversal, \
    and actual polynomial norm declarations, including private helpers: \
    standard Lean logical foundations only."
