/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.AdjoinRootMinpolyDegree
public import Aglib.FieldTheory.FieldCharpolyPower
public import Lean.Util.CollectAxioms

/-! Consumers of the original root-evaluation scalar map and relative degree. -/

@[expose] public noncomputable section

open Polynomial

namespace AglibTest.AdjoinRootMinpolyDegree

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] {q : k[X]}
  [Algebra (AdjoinRoot q) L] [IsScalarTower k (AdjoinRoot q) L]

/-- The original map is literally the simple-field inclusion after the equivalence. -/
theorem originalScalarMap (a : L) (hq : minpoly k a = q)
    (hroot : algebraMap (AdjoinRoot q) L (AdjoinRoot.root q) = a) :
    (IntermediateField.adjoin k {a}).val.comp
        (AdjoinRoot.minpolyEquivAdjoin a hq).toAlgHom =
      IsScalarTower.toAlgHom k (AdjoinRoot q) L :=
  AdjoinRoot.minpolyEquivAdjoin_comp_inclusion a hq hroot

/-- The relative degree refers to the existing root-presentation scalar structure. -/
theorem originalDegree (a : L) (hq : minpoly k a = q)
    (hroot : algebraMap (AdjoinRoot q) L (AdjoinRoot.root q) = a) :
    Module.finrank (IntermediateField.adjoin k {a}) L = Module.finrank (AdjoinRoot q) L :=
  AdjoinRoot.finrank_adjoin_eq_of_minpoly_eq a hq hroot

/-- The field characteristic polynomial uses the original named quotient degree. -/
theorem originalCharpoly [Infinite k] (a : L) (hq : minpoly k a = q)
    (hroot : algebraMap (AdjoinRoot q) L (AdjoinRoot.root q) = a) :
    (Algebra.lmul k L a).charpoly = q ^ Module.finrank (AdjoinRoot q) L := by
  rw [Algebra.charpoly_lmul_eq_minpoly_pow,
    AdjoinRoot.finrank_adjoin_eq_of_minpoly_eq a hq hroot, hq]

open Lean in
run_cmd do
  for name in #[``AdjoinRoot.minpolyEquivAdjoin, ``AdjoinRoot.minpolyEquivAdjoin_root,
      ``AdjoinRoot.minpolyEquivAdjoin_comp_inclusion, ``AdjoinRoot.minpolyEquivAdjoin_algebraMap,
      ``AdjoinRoot.finrank_adjoin_eq_of_minpoly_eq, ``originalScalarMap, ``originalDegree,
      ``originalCharpoly] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual root-presentation degrees use only standard foundations."

end AglibTest.AdjoinRootMinpolyDegree
