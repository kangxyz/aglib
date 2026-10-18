/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.AdjoinRootCoefficientEquiv
import Lean.Util.CollectAxioms

/-! Direct consumers of literal coefficient extension over arbitrary
commutative rings, with actual quotient-element and inverse formulas. -/

open Polynomial AdjoinRoot

namespace AglibTest.AdjoinRootCoefficientEquiv

variable {k L : Type*} [CommRing k] [CommRing L] [Algebra k L]

/-- The universal construction has no irreducibility or field premise. -/
theorem actual_hom_square (p q : k[X]) (f : AdjoinRoot p →ₐ[k] AdjoinRoot q)
    (x : AdjoinRoot p) :
    coefficientExtension (L := L) f (coefficientMap p x) = coefficientMap q (f x) :=
  coefficientExtension_coefficientMap f x

/-- Equivalence transport commutes on every original element, not just the root. -/
theorem actual_equiv_square (p q : k[X]) (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q)
    (x : AdjoinRoot p) :
    coefficientEquiv (L := L) e (coefficientMap p x) = coefficientMap q (e x) :=
  coefficientEquiv_coefficientMap e x

/-- The constructed scalar extension has an actual two-sided inverse. -/
theorem inverse_on_all_elements (p q : k[X]) (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q)
    (x : AdjoinRoot (p.map (algebraMap k L))) :
    (coefficientEquiv (L := L) e).symm (coefficientEquiv (L := L) e x) = x :=
  (coefficientEquiv (L := L) e).symm_apply_apply x

/-- Extending the identity is literally the identity on the enlarged algebra. -/
theorem identity (p : k[X]) :
    coefficientExtension (L := L) (AlgHom.id k (AdjoinRoot p)) =
      AlgHom.id L (AdjoinRoot (p.map (algebraMap k L))) := by
  apply AdjoinRoot.algHom_ext
  simp only [coefficientExtension_root, AlgHom.id_apply, coefficientMap_root]

/-- Actual homomorphism composition is preserved under coefficient extension. -/
theorem composition (p q r : k[X]) (f : AdjoinRoot p →ₐ[k] AdjoinRoot q)
    (g : AdjoinRoot q →ₐ[k] AdjoinRoot r) :
    coefficientExtension (L := L) (g.comp f) =
      (coefficientExtension (L := L) g).comp (coefficientExtension (L := L) f) := by
  apply AdjoinRoot.algHom_ext
  simp only [coefficientExtension_root, AlgHom.comp_apply, coefficientExtension_coefficientMap]

/-- Even the zero polynomial is allowed in this algebraic transport lemma. -/
theorem zero_polynomial :
    coefficientExtension (L := L) (AlgHom.id k (AdjoinRoot (0 : k[X]))) =
      AlgHom.id L (AdjoinRoot ((0 : k[X]).map (algebraMap k L))) :=
  identity 0

end AglibTest.AdjoinRootCoefficientEquiv

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModule := `Aglib.RingTheory.AdjoinRootCoefficientEquiv
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == sourceModule then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  if names.size < 7 then
    throwError "The native source declarations are missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.AdjoinRootCoefficientEquiv).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} root coefficient-extension and consumer declarations: \
    standard axioms only."
