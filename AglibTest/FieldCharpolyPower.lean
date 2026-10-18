/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.FieldCharpolyPower
public import Mathlib.Algebra.CharZero.Infinite
public import Lean.Util.CollectAxioms

/-! Regression tests for the actual field multiplication characteristic polynomial. -/

@[expose] public noncomputable section

namespace AglibTest.FieldCharpolyPower

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L]

/-- Evaluation is the norm of scalar minus the original element. -/
theorem evalAtScalar (a : L) (t : k) :
    (Algebra.lmul k L a).charpoly.eval t =
      Algebra.norm k (algebraMap k L t - a) :=
  Algebra.eval_charpoly_lmul a t

/-- No infinite-base hypothesis is needed inside the simple extension. -/
theorem simpleGenerator (a : L) :
    (Algebra.lmul k (IntermediateField.adjoin k {a})
      (IntermediateField.AdjoinSimple.gen k a)).charpoly = minpoly k a :=
  Algebra.charpoly_lmul_adjoin_gen a

/-- The exponent is the actual relative degree over the simple intermediate field. -/
theorem infiniteBase [Infinite k] (a : L) :
    (Algebra.lmul k L a).charpoly =
      (minpoly k a) ^ Module.finrank (IntermediateField.adjoin k {a}) L :=
  Algebra.charpoly_lmul_eq_minpoly_pow a

/-- Characteristic-zero consumers obtain the infinite-base theorem. -/
theorem characteristicZero [CharZero k] (a : L) :
    (Algebra.lmul k L a).charpoly =
      (minpoly k a) ^ Module.finrank (IntermediateField.adjoin k {a}) L :=
  Algebra.charpoly_lmul_eq_minpoly_pow a

open Lean in
run_cmd do
  for name in #[``Algebra.eval_charpoly_lmul, ``Algebra.charpoly_lmul_adjoin_gen,
      ``Algebra.charpoly_lmul_eq_minpoly_pow, ``evalAtScalar, ``simpleGenerator,
      ``infiniteBase, ``characteristicZero] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Field multiplication characteristic polynomials use only standard foundations."

end AglibTest.FieldCharpolyPower
