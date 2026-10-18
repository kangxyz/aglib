/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalTranslation
import Lean.Util.CollectAxioms

/-! Direct consumers retaining rational translation and the original linear-place residues. -/

open Polynomial Polynomial.LocalResidue
open MilnorK MilnorK.PolynomialResidue
open MilnorK.PolynomialNorm

namespace AglibTest.GeneralMilnorPolynomialNormRationalTranslation

variable {k : Type*} [Field k]

/-- The original rational linear uniformizer translates literally to the variable. -/
theorem actual_uniformizer (a : k) :
    RatFunc.translationHom a (RatFunc.X - RatFunc.C a) = RatFunc.X := by
  simp only [map_sub, RatFunc.translationHom_X, RatFunc.translationHom_C, add_sub_cancel_right]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩
local instance (a : k) : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩

/-- The residue identification itself works in every characteristic. -/
theorem literal_residue_translation (a : k) (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    map n (linearRootEquiv a).toRingHom (residueAt (X - C a) n x) =
      map n (InfinityResidue.rootXEquiv k).toRingHom
        (residueAt (X : k[X]) n (map (n + 1) (RatFunc.translationHom a) x)) :=
  residueAt_linear_eq_residueAt_X_translation a n x

variable [CharZero k] (p : MonicIrreducible k)

/-- The actual rational norm translates on every class, without normality. -/
theorem arbitrary_class (a : k) (n : ℕ) (x : K (RatFunc (AdjoinRoot p.val)) n) :
    map n (RatFunc.translationHom a) (rationalFunctionNorm n p x) =
      rationalFunctionNorm n p
        (map n (RatFunc.translationHom (algebraMap k (AdjoinRoot p.val) a)) x) :=
  rationalFunctionNorm_translation p a n x

/-- Degree zero is included in the same covariance statement. -/
theorem empty_degree (a : k) (x : K (RatFunc (AdjoinRoot p.val)) 0) :
    map 0 (RatFunc.translationHom a) (rationalFunctionNorm 0 p x) =
      rationalFunctionNorm 0 p
        (map 0 (RatFunc.translationHom (algebraMap k (AdjoinRoot p.val) a)) x) :=
  rationalFunctionNorm_translation p a 0 x

local instance (a : AdjoinRoot p.val) : Fact (Irreducible (X - C a)) :=
  ⟨irreducible_X_sub_C a⟩

/-- The complete prime-normal norm-residue square now holds at every actual linear place. -/
theorem actual_linear_prime_square [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (a : k) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (linearRootEquiv a).toRingHom
      (residueAt (X - C a) n (rationalFunctionNorm (n + 1) p x)) =
      polynomialNorm n p
        (map n (linearRootEquiv (algebraMap k (AdjoinRoot p.val) a)).toRingHom
          (residueAt (X - C (algebraMap k (AdjoinRoot p.val) a)) n x)) :=
  residueAt_linear_rationalFunctionNorm_prime p hp a n x

end AglibTest.GeneralMilnorPolynomialNormRationalTranslation

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModules := #[`Aglib.FieldTheory.RatFuncTranslation,
    `Aglib.KTheory.MilnorK.Norm.Polynomial.RationalTranslation]
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if sourceModules.contains env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  if names.size < 12 then
    throwError "The actual rational-translation source declarations are missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.GeneralMilnorPolynomialNormRationalTranslation).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} rational-translation declarations: standard axioms only."
