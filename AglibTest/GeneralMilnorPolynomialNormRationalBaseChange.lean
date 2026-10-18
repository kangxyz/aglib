/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalBaseChange
import Lean.Util.CollectAxioms

/-! Full rational coefficient branch sums, including extension to another
literal root field, without any norm tower or presentation-independence input. -/

open Polynomial Polynomial.LocalResidue
open MilnorK MilnorK.PolynomialResidue
open MilnorK.PolynomialNorm

namespace AglibTest.GeneralMilnorPolynomialNormRationalBaseChange

variable {k H : Type*} [Field k] [Field H]

/-- Every original branch, not merely a selected one, is carried to its
literal rational coefficient presentation. -/
theorem actual_branch_bijection (φ : k →+* H) (p : MonicIrreducible k)
    (q : {q // q ∈ placesAbove φ p}) :
    (rationalCoefficientPlacesEquiv φ p q).val = rationalCoefficientPolynomial q.val :=
  rationalCoefficientPlacesEquiv_apply φ p q

open scoped Classical in
/-- The full branch sum over an arbitrary literal root field is available on
every input class. This is the form needed in the finite-place assembly. -/
theorem full_root_field_branch_sum [CharZero k]
    (n : ℕ) (p h : MonicIrreducible k) (x : K (RatFunc (AdjoinRoot p.val)) n) :
    map n (fractionMap (algebraMap k (AdjoinRoot h.val))) (rationalFunctionNorm n p x) =
      ∑ q ∈ (placesAbove (algebraMap k (AdjoinRoot h.val)) p).attach,
        rationalFunctionNorm n q.val
          (map n (fractionMap (adjoinRootMap (algebraMap k (AdjoinRoot h.val))
            p.val q.val.val
            ((mem_placesAbove _ p q.val).mp q.property))) x) :=
  rationalFunctionNorm_restrict _ n p x

open scoped Classical in
/-- Degree zero is included in the same complete sum, with no positive-degree
or symbol-generator restriction. -/
theorem degree_zero_full_sum [CharZero k]
    (φ : k →+* H) (p : MonicIrreducible k) (x : K (RatFunc (AdjoinRoot p.val)) 0) :
    map 0 (fractionMap φ) (rationalFunctionNorm 0 p x) =
      ∑ q ∈ (placesAbove φ p).attach,
        rationalFunctionNorm 0 q.val
          (map 0 (fractionMap (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property))) x) :=
  rationalFunctionNorm_restrict φ 0 p x

end AglibTest.GeneralMilnorPolynomialNormRationalBaseChange

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `MilnorK.PolynomialNorm.rationalCoefficient_map_fractionMap,
    `MilnorK.PolynomialNorm.exists_rationalCoefficient_factor,
    `MilnorK.PolynomialNorm.rationalCoefficientPlacesEquiv,
    `MilnorK.PolynomialNorm.rationalCoefficientPlacesEquiv_apply,
    `MilnorK.PolynomialNorm.rationalCoefficientAlgEquiv_comp_adjoinRootMap,
    `MilnorK.PolynomialNorm.rationalCoefficientAlgEquiv_symm_comp_fractionMap,
    `MilnorK.PolynomialNorm.rationalFunctionNorm_restrict,
    `MilnorK.PolynomialNorm.rationalFunctionNorm_comp_restrict,
    `AglibTest.GeneralMilnorPolynomialNormRationalBaseChange.actual_branch_bijection,
    `AglibTest.GeneralMilnorPolynomialNormRationalBaseChange.full_root_field_branch_sum,
    `AglibTest.GeneralMilnorPolynomialNormRationalBaseChange.degree_zero_full_sum]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Checked the full actual rational coefficient norm branch sum: standard axioms only."
