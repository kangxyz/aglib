/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalLinear
import Lean.Util.CollectAxioms

/-! Direct all-characteristic consumers of the linear rational norm-residue squares. -/

open Polynomial Polynomial.LocalResidue
open MilnorK MilnorK.PolynomialResidue
open MilnorK.PolynomialNorm
open MilnorK.K3.PolynomialNorm (rootEvaluation)

namespace AglibTest.GeneralMilnorPolynomialNormRationalLinear

variable {k : Type*} [Field k] (p : MonicIrreducible k) (hp : p.val.natDegree = 1)

/-- Every rational class uses the actual coefficient root evaluation. -/
theorem arbitrary_class (n : ℕ) (x : K (RatFunc (AdjoinRoot p.val)) n) :
    rationalFunctionNorm n p x = map n (fractionMap (rootEvaluation p hp)) x := by
  rw [rationalFunctionNorm_eq_map_rootEvaluation p hp]

/-- The norm formula includes degree zero. -/
theorem empty_degree (x : K (RatFunc (AdjoinRoot p.val)) 0) :
    rationalFunctionNorm 0 p x = map 0 (fractionMap (rootEvaluation p hp)) x :=
  arbitrary_class p hp 0 x

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩
local instance : Fact (Irreducible (X : (AdjoinRoot p.val)[X])) := ⟨irreducible_X⟩

/-- The finite square retains the original map of polynomial quotient fields. -/
theorem literal_finite_quotient_square (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    residueAt (X : k[X]) n (rationalFunctionNorm (n + 1) p x) =
      map n (adjoinRootMap (rootEvaluation p hp) X X (by simp))
        (residueAt (X : (AdjoinRoot p.val)[X]) n x) :=
  residueAt_X_rationalFunctionNorm_linear p hp n x

include hp in
/-- Coefficient-field normalization gives the genuine finite norm-residue square. -/
theorem normalized_finite_square (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (InfinityResidue.rootXEquiv k).toRingHom
        (residueAt (X : k[X]) n (rationalFunctionNorm (n + 1) p x)) =
      polynomialNorm n p
        (map n (InfinityResidue.rootXEquiv (AdjoinRoot p.val)).toRingHom
          (residueAt (X : (AdjoinRoot p.val)[X]) n x)) :=
  residueAt_X_rationalFunctionNorm_linear_normalized p hp n x

include hp in
/-- Infinity also commutes with the original coefficient norm on every class. -/
theorem actual_infinity_square (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    InfinityResidue.residue k n (rationalFunctionNorm (n + 1) p x) =
      polynomialNorm n p (InfinityResidue.residue (AdjoinRoot p.val) n x) :=
  infinityResidue_rationalFunctionNorm_linear p hp n x

end AglibTest.GeneralMilnorPolynomialNormRationalLinear

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModule := `Aglib.KTheory.MilnorK.Norm.Polynomial.RationalLinear
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == sourceModule then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  if names.size < 6 then
    throwError "The actual linear rational-norm source declarations are missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.GeneralMilnorPolynomialNormRationalLinear).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} linear rational-norm declarations: standard axioms only."
