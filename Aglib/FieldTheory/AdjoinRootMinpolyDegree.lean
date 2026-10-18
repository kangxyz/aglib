/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Actual root presentations and relative degrees

An identified minimal polynomial presents the actual simple intermediate field.
The equivalence preserves the original scalar map whenever it sends the quotient
root to the specified element; consequently the two relative degrees agree.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] {q : k[X]}

/-- The root presentation of the actual simple intermediate field, with a named
polynomial identified with the minimal polynomial. -/
def minpolyEquivAdjoin (a : L) (hq : minpoly k a = q) :
    AdjoinRoot q ≃ₐ[k] IntermediateField.adjoin k {a} :=
  (algEquivOfEq k q (minpoly k a) hq.symm).trans
    (IntermediateField.adjoinRootEquivAdjoin k (Algebra.IsIntegral.isIntegral (R := k) a))

/-- The presentation equivalence sends the original quotient root to the actual
generator of the simple intermediate field. -/
@[simp]
theorem minpolyEquivAdjoin_root (a : L) (hq : minpoly k a = q) :
    minpolyEquivAdjoin a hq (root q) = IntermediateField.AdjoinSimple.gen k a := by
  simp only [minpolyEquivAdjoin, AlgEquiv.trans_apply, algEquivOfEq_root,
    IntermediateField.adjoinRootEquivAdjoin_apply_root]

variable [Algebra (AdjoinRoot q) L] [IsScalarTower k (AdjoinRoot q) L]

/-- The equivalence followed by the literal intermediate-field inclusion equals
the originally supplied algebra map, not a replacement algebra structure. -/
theorem minpolyEquivAdjoin_comp_inclusion (a : L) (hq : minpoly k a = q)
    (hroot : algebraMap (AdjoinRoot q) L (root q) = a) :
    (IntermediateField.adjoin k {a}).val.comp (minpolyEquivAdjoin a hq).toAlgHom =
      IsScalarTower.toAlgHom k (AdjoinRoot q) L := by
  apply AdjoinRoot.algHom_ext
  simpa using hroot.symm

/-- Pointwise compatibility with the original root-evaluation algebra map. -/
theorem minpolyEquivAdjoin_algebraMap (a : L) (hq : minpoly k a = q)
    (hroot : algebraMap (AdjoinRoot q) L (root q) = a) (x : AdjoinRoot q) :
    algebraMap (IntermediateField.adjoin k {a}) L (minpolyEquivAdjoin a hq x) =
      algebraMap (AdjoinRoot q) L x := by
  exact AlgHom.congr_fun (minpolyEquivAdjoin_comp_inclusion a hq hroot) x

/-- Relative degree over the actual simple intermediate field equals relative
degree over the original named root presentation and its existing scalar map. -/
theorem finrank_adjoin_eq_of_minpoly_eq (a : L) (hq : minpoly k a = q)
    (hroot : algebraMap (AdjoinRoot q) L (root q) = a) :
    Module.finrank (IntermediateField.adjoin k {a}) L = Module.finrank (AdjoinRoot q) L := by
  symm
  apply Algebra.finrank_eq_of_equiv_equiv (minpolyEquivAdjoin a hq).toRingEquiv
    (RingEquiv.refl L)
  apply RingHom.ext
  intro x
  exact minpolyEquivAdjoin_algebraMap a hq hroot x

end AdjoinRoot
