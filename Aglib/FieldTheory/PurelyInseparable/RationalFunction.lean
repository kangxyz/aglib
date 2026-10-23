/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.PurelyInseparable.RationalEvaluation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-! # Perfect closure of a function field over separably closed constants

The extension is the actual relative perfect closure inside an algebraic
closure. No reducedness or domain assertion about a tensor product is used.
-/

@[expose] public noncomputable section

open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace Field

universe u

/-- The actual purely inseparable perfect extension used to enlarge constants. -/
abbrev perfectFunctionField (E : Type u) [Field E] :=
  perfectClosure E (AlgebraicClosure E)

/-- An algebraic function field over a possibly imperfect separably closed
constant field has an actual purely inseparable extension algebraic over the
rational functions of the algebraic closure of its constants. The equality
retains the original rational-function map and the original field inclusion. -/
theorem exists_ratFuncAlgebra_perfectFunctionField
    (k E : Type u) [Field k] [IsSepClosed k] [Field E]
    [Algebra (RatFunc k) E] [Algebra.IsAlgebraic (RatFunc k) E] :
    ∃ a : Algebra (RatFunc (AlgebraicClosure k)) (perfectFunctionField E),
      letI := a
      Algebra.IsAlgebraic (RatFunc (AlgebraicClosure k)) (perfectFunctionField E) ∧
        (algebraMap (RatFunc (AlgebraicClosure k)) (perfectFunctionField E)).comp
          (algebraMap (RatFunc k) (RatFunc (AlgebraicClosure k))) =
        (algebraMap E (perfectFunctionField E)).comp (algebraMap (RatFunc k) E) := by
  let L := perfectFunctionField E
  let K := AlgebraicClosure k
  let : Algebra k E := Algebra.compHom E (algebraMap k (RatFunc k))
  let : Algebra (RatFunc k) L := Algebra.compHom L (algebraMap (RatFunc k) E)
  have : IsScalarTower (RatFunc k) E L := IsScalarTower.of_compHom _ _ _
  let : Algebra k L := Algebra.compHom L (algebraMap k (RatFunc k))
  have : IsScalarTower k (RatFunc k) L := by
    constructor
    intro x y z
    change (x • y : RatFunc k) • z =
      (algebraMap k (RatFunc k) x) • (y • z)
    rw [RatFunc.smul_eq_C_mul, ← RatFunc.algebraMap_eq_C]
    exact (Algebra.toModule (R := RatFunc k) (A := L)).mul_smul
      (algebraMap k (RatFunc k) x) y z
  let c : K →ₐ[k] L := Classical.choice inferInstance
  let : Algebra K L := c.toRingHom.toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' c.comp_algebraMap.symm
  obtain ⟨a, hR⟩ := RatFunc.exists_algebraicConstantsAlgebra k K L
  let := a
  have : Algebra.IsAlgebraic (RatFunc k) L := Algebra.IsAlgebraic.trans (RatFunc k) E L
  refine ⟨a, ?_, hR⟩
  exact Algebra.IsAlgebraic.ringHom_of_comp_eq
    (algebraMap (RatFunc k) (RatFunc K)) (RingHom.id L)
    (algebraMap (RatFunc k) (RatFunc K)).injective Function.surjective_id
    (by
      change (algebraMap (RatFunc K) L).comp (algebraMap (RatFunc k) (RatFunc K)) =
        (RingHom.id L).comp (algebraMap (RatFunc k) L)
      rw [RingHom.id_comp]
      exact hR)

end Field
