/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.One
import Lean.Util.CollectAxioms

/-! Direct consumers of all-degree split norms, ordinary degree-one norms,
degree-one presentation independence and mixed symbols in every degree.
Legacy imports ensure all audited declarations have checked proof bodies. -/

open Polynomial Polynomial.LocalResidue
open MilnorK MilnorK.PolynomialResidue MilnorK.PolynomialNorm

namespace AglibTest.GeneralMilnorPolynomialNormOne

variable {k L : Type*} [Field k] [Field L]

/-- Every-degree linear normalization is valid without characteristic assumptions. -/
theorem actual_linear_norm (n : ℕ) (q : MonicIrreducible L)
    (hq : q.val.natDegree = 1) (z : K (AdjoinRoot q.val) n) :
    polynomialNorm n q z =
      map n (MilnorK.K3.PolynomialNorm.rootEvaluation q hq) z :=
  LinearMap.congr_fun (polynomialNorm_eq_map_rootEvaluation n q hq) z

open scoped Classical in
/-- Every actual linear branch occurs in the all-degree split formula. -/
theorem all_split_branches [CharZero k] (φ : k →+* L) (n : ℕ)
    (p : MonicIrreducible k) (hp : (p.val.map φ).Splits) (z : K (AdjoinRoot p.val) n) :
    map n φ (polynomialNorm n p z) =
      ∑ q ∈ (placesAbove φ p).attach,
        map n (MilnorK.K3.PolynomialNorm.splitBranchMap φ p hp q) z :=
  polynomialNorm_restrict_of_splits φ n p hp z

/-- The branch-to-embedding correspondence is bijective, not only injective. -/
theorem all_embeddings [Algebra k L] (p : MonicIrreducible k)
    (hp : (p.val.map (algebraMap k L)).Splits) :
    Function.Bijective (splitBranchAlgHom p hp) :=
  ⟨splitBranchAlgHom_injective p hp, splitBranchAlgHom_surjective p hp⟩

variable [CharZero k]

/-- Every actual degree-one class has the ordinary determinant norm. -/
theorem ordinary_norm_on_all_classes (p : MonicIrreducible k)
    (z : K (AdjoinRoot p.val) 1) :
    oneEquiv k (polynomialNorm 1 p z) =
      Additive.ofMul (Units.map (Algebra.norm k) (oneEquiv (AdjoinRoot p.val) z).toMul) :=
  oneEquiv_polynomialNorm p z

/-- Degree-one presentation independence requires only the actual algebra
equivalence between the two root fields. -/
theorem degree_one_presentation_independence (p q : MonicIrreducible k)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) (z : K (AdjoinRoot p.val) 1) :
    polynomialNorm 1 q (map 1 e.toRingHom z) = polynomialNorm 1 p z :=
  polynomialNorm_one_map_algEquiv p q e z

/-- The base factor is an arbitrary quotient class, in every degree. -/
theorem arbitrary_base_class (m : ℕ) (p : MonicIrreducible k)
    (x : K k m) (a : Additive (AdjoinRoot p.val)ˣ) :
    polynomialNorm (m + 1) p
      (productUnit m (map m (algebraMap k (AdjoinRoot p.val)) x) a) =
        productUnit m x (Additive.ofMul (Units.map (Algebra.norm k) a.toMul)) :=
  polynomialNorm_productUnit_constants m p x a

/-- The empty base tuple is included, giving the ordinary norm of one unit. -/
theorem empty_base_tuple (p : MonicIrreducible k) (b : (AdjoinRoot p.val)ˣ) :
    polynomialNorm 1 p (symbol (Fin.snoc
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom ∘ Fin.elim0) b)) =
        symbol (Fin.snoc Fin.elim0 (Units.map (Algebra.norm k) b)) :=
  polynomialNorm_symbol_constants_unit 0 p Fin.elim0 b

/-- Arbitrarily long constant tuples retain their coordinates, while the final
unit is replaced by its ordinary field norm. -/
theorem all_degree_mixed_symbol (m : ℕ) (p : MonicIrreducible k)
    (a : SymbolTuple k m) (b : (AdjoinRoot p.val)ˣ) :
    polynomialNorm (m + 1) p
      (symbol (Fin.snoc (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom ∘ a) b)) =
        symbol (Fin.snoc a (Units.map (Algebra.norm k) b)) :=
  polynomialNorm_symbol_constants_unit m p a b

end AglibTest.GeneralMilnorPolynomialNormOne

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
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
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorPolynomialNormOne]
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
  logInfo m!"Checked {names.size} split/degree-one norm and general Milnor declarations: \
    standard axioms only."
