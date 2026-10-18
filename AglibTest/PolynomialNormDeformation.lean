/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialNormDeformation
public import Lean.Util.CollectAxioms

/-! # Literal polynomial-norm deformation and multiplicity consumers -/

@[expose] public noncomputable section

open Polynomial MilnorK.K3
open PolynomialResidue PolynomialNorm UniqueFactorizationMonoid

namespace AglibTest.PolynomialNormDeformation

variable {k : Type*} [Field k]

/-- The recurrence uses the constructed norms and allows arbitrary nonzero
polynomials in the other two slots, including their poles at infinity. -/
theorem actual_norm_recurrence (p q A B : k[X]) (hp : p.Monic) (hq : q.Monic)
    (hd : p.natDegree = q.natDegree) (hA : A ≠ 0) (hB : B ≠ 0)
    (hpc : IsCoprime p (A * B)) (hqc : IsCoprime q (A * B))
    (hmod : A * B ∣ p - q) :
    factorNormSum p A B hp hpc = factorNormSum q A B hq hqc :=
  factorNormSum_eq_of_monic_deformation p q A B hp hq hd hA hB hpc hqc hmod

/-- At an irreducible endpoint the recurrence has the original norm and literal
quotient-unit symbol as its left side. -/
theorem actual_irreducible_recurrence (p : MonicIrreducible k) (q A B : k[X])
    (hq : q.Monic) (hd : p.val.natDegree = q.natDegree) (hA : A ≠ 0) (hB : B ≠ 0)
    (hpc : IsCoprime p.val (A * B)) (hqc : IsCoprime q (A * B))
    (hrA : ¬ p.val ∣ A) (hrB : ¬ p.val ∣ B) (hmod : A * B ∣ p.val - q) :
    polynomialNorm p
      (MilnorK.K2.symbol (quotientUnit p.val A hrA) (quotientUnit p.val B hrB)) =
      factorNormSum q A B hq hqc := by
  rw [← factorNormSum_irreducible p A B hpc hrA hrB]
  exact actual_norm_recurrence p.val q A B p.property.1 hq hd hA hB hpc hqc hmod

open scoped Classical in
/-- A double factor is retained twice, with no squarefreeness assumption. -/
theorem repeated_factor_count (p : MonicIrreducible k) :
    (factorPlaces (p.val ^ 2) (pow_ne_zero 2 p.property.2.ne_zero)).count p = 2 := by
  classical
  rw [count_factorPlaces, normalizedFactors_pow, normalizedFactors_irreducible p.property.2,
    p.property.1.normalize_eq_self]
  simp

/-- Places dividing either other entry vanish because the first quotient
reduces to one, even when those entries are not local units. -/
theorem actual_bad_place (p q A B : k[X]) (hp : p.Monic) (hq : q.Monic)
    (hA : A ≠ 0) (hB : B ≠ 0) (hpc : IsCoprime p (A * B))
    (hqc : IsCoprime q (A * B)) (hmod : A * B ∣ p - q)
    (r : MonicIrreducible k) (hr : r.val ∣ A * B) :
    residueAt r.val
      (symbol3 (polynomialUnit p hp.ne_zero / polynomialUnit q hq.ne_zero)
        (polynomialUnit A hA) (polynomialUnit B hB)) = 0 := by
  have hrp : ¬ r.val ∣ p := fun h => r.property.2.not_isUnit (hpc.isUnit_of_dvd' h hr)
  have hrq : ¬ r.val ∣ q := fun h => r.property.2.not_isUnit (hqc.isUnit_of_dvd' h hr)
  exact residueAt_polynomial_ratio_eq_zero r.val p q hp.ne_zero hq.ne_zero hrp hrq
    (quotientUnit_eq_of_dvd_sub r p q hrp hrq (dvd_trans hr hmod)) _ _

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModule := `Aglib.KTheory.MilnorK.K3.PolynomialNormDeformation
  let consumerPrefix := `AglibTest.PolynomialNormDeformation
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == libraryModule then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if consumerPrefix.isPrefixOf name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Deformation declaration {name} is absent from the kernel environment"
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} literal polynomial-norm deformation declarations and consumers, \
    including private helpers: only standard Lean logical foundations."

end AglibTest.PolynomialNormDeformation
