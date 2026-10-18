/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.FieldTheory.RationalCoefficientRoot
import Lean.Util.CollectAxioms

/-! Direct consumers of actual rational coefficient root fields and inversion. -/

open Polynomial AdjoinRoot
open scoped RatFunc

attribute [local instance] Polynomial.algebra

namespace AglibTest.RationalCoefficientRoot

variable {k : Type*} [Field k] (p : k[X]) [Fact (Irreducible p)] (hp : p.Monic)

include hp in
/-- Irreducibility is proved over the actual rational-function field. -/
theorem irreducible_constant_extension :
    Irreducible (p.map (RatFunc.C : k →+* RatFunc k)) :=
  hp.irreducible_map_ratFunc_C Fact.out

/-- The original selected root maps to its literal constant rational function. -/
theorem actual_root :
    rationalCoefficientAlgEquiv p hp (AdjoinRoot.root (p.map RatFunc.C)) =
      RatFunc.C (AdjoinRoot.root p) :=
  rationalCoefficientAlgEquiv_root p hp

/-- The compatibility holds on every original root-field element. -/
theorem actual_coefficient_square (x : AdjoinRoot p) :
    rationalCoefficientAlgEquiv p hp
      (AdjoinRoot.coefficientMap (L := RatFunc k) p x) = RatFunc.C x :=
  rationalCoefficientAlgEquiv_coefficientMap p hp x

/-- The actual rational coefficient field map is not replaced by an assumed scalar map. -/
theorem actual_base_square (x : RatFunc k) :
    rationalCoefficientAlgEquiv p hp
      (algebraMap (RatFunc k) (AdjoinRoot (p.map RatFunc.C)) x) =
      Polynomial.LocalResidue.fractionMap (algebraMap k (AdjoinRoot p)) x :=
  rationalCoefficientAlgEquiv_algebraMap p hp x

/-- Surjectivity provides the actual inverse on every rational function over the root field. -/
theorem actual_two_sided_inverse (x : RatFunc (AdjoinRoot p)) :
    rationalCoefficientAlgEquiv p hp ((rationalCoefficientAlgEquiv p hp).symm x) = x :=
  (rationalCoefficientAlgEquiv p hp).apply_symm_apply x

/-- Inversion intertwines through the literal upper quotient map on every class. -/
theorem actual_inversion (x : AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k))) :
    letI : Fact (Irreducible (p.map (RatFunc.C : k →+* RatFunc k))) :=
      ⟨hp.irreducible_map_ratFunc_C Fact.out⟩
    rationalCoefficientAlgEquiv p hp
      (Polynomial.LocalResidue.adjoinRootMap (RatFunc.inversion k).toRingHom
        (p.map RatFunc.C) (p.map RatFunc.C) (by rw [Polynomial.map_ratFunc_C_inversion]) x) =
      RatFunc.inversion (AdjoinRoot p) (rationalCoefficientAlgEquiv p hp x) :=
  RingHom.congr_fun (rationalCoefficientAlgEquiv_comp_inversion p hp) x

end AglibTest.RationalCoefficientRoot

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModule := `Aglib.FieldTheory.RationalCoefficientRoot
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == sourceModule then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.RationalCoefficientRoot).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} rational coefficient root declarations: standard axioms only."
