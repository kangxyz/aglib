/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialNormRootRecurrence
public import Lean.Util.CollectAxioms

/-! # Actual root-symbol recurrence and local-kernel reduction consumers -/

@[expose] public noncomputable section

open Polynomial MilnorK.K3
open PolynomialResidue PolynomialNorm MilnorK.K2

namespace AglibTest.PolynomialNormRootRecurrence

variable {k : Type*} [Field k]

/-- The literal three-place computation keeps its constant-coefficient term
and its sign in the original integral Milnor group. -/
theorem actual_root_recurrence (p q : MonicIrreducible k) (hpq : p ≠ q)
    (hp0 : p.val.coeff 0 ≠ 0) (hq0 : q.val.coeff 0 ≠ 0) :
    polynomialNorm p
      (symbol (quotientUnit p.val q.val (not_dvd_of_ne q p hpq.symm)) (rootUnit p hp0)) =
      polynomialNorm q
        (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq)) (rootUnit q hq0)) -
      symbol (constantCoeffUnit p hp0) (constantCoeffUnit q hq0) +
      (p.val.natDegree * q.val.natDegree) • symbol (-1 : kˣ) (-1) :=
  polynomialNorm_root_reciprocity p q hpq hp0 hq0

/-- Two degree-one places contribute one copy of the sign symbol, rather
than zero. This checks the smallest odd-degree case of the recurrence. -/
theorem degree_one_sign (p q : MonicIrreducible k) (hpq : p ≠ q)
    (hp0 : p.val.coeff 0 ≠ 0) (hq0 : q.val.coeff 0 ≠ 0)
    (hpdeg : p.val.natDegree = 1) (hqdeg : q.val.natDegree = 1) :
    polynomialNorm p
      (symbol (quotientUnit p.val q.val (not_dvd_of_ne q p hpq.symm)) (rootUnit p hp0)) =
      polynomialNorm q
        (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq)) (rootUnit q hq0)) -
      symbol (constantCoeffUnit p hp0) (constantCoeffUnit q hq0) +
      symbol (-1 : kˣ) (-1) := by
  simpa only [hpdeg, hqdeg, Nat.one_mul, one_smul] using
    actual_root_recurrence p q hpq hp0 hq0

/-- The infinity calculation remains valid with arbitrary other entries. -/
theorem infinity_with_arbitrary_entries (p : k[X]) (hp : p.Monic)
    (a b : (RatFunc k)ˣ) (n : ℤ) :
    InfinityResidue.residue k (n • symbol3 (polynomialUnit p hp.ne_zero) a b) =
      n • (p.natDegree • InfinityResidue.residue k
        (symbol3 (InfinityResidue.variableUnit k) a b)) := by
  rw [map_zsmul, residue_monic_first p hp a b]

/-- The possible `X` factor is a genuine diagonal symbol. Its two-torsion
sign contribution is not erased or omitted. -/
theorem actual_diagonal_root (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) :
    polynomialNorm p (symbol (rootUnit p hp0) (rootUnit p hp0)) =
      symbol ((-1) ^ p.val.natDegree * constantCoeffUnit p hp0) (-1) := by
  have hneg : Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom (-1) =
      (-1 : (AdjoinRoot p.val)ˣ) := by
    apply Units.ext
    change algebraMap k (AdjoinRoot p.val) (-1) = -1
    rw [map_neg, map_one]
  rw [symbol_self, ← hneg, polynomialNorm_root_constant_coefficient]

section LocalKernel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R k] [IsFractionRing R k]

/-- Instantiating the reduction with the two actual DVR kernels states exactly
which smaller-place identities still have to be proved. This conditional
consumer does not claim principal-unit preservation. The first entry is an
arbitrary root-field unit, with no valuation or integral-lift assumption. -/
theorem actual_local_vanishing_reduction
    (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) {π : R} (hπ : Irreducible π)
    (hconstant : ∀ c : kˣ,
      tame (MilnorK.K2.DVR.data hπ)
        (symbol c ((-1) ^ p.val.natDegree * constantCoeffUnit p hp0)) = 0 ∧
      specialize (MilnorK.K2.DVR.data hπ) (MilnorK.K2.DVR.unitReductionCompatible hπ)
        (symbol c ((-1) ^ p.val.natDegree * constantCoeffUnit p hp0)) = 0)
    (hlower : ∀ (q : MonicIrreducible k), q.val.natDegree < p.val.natDegree →
      ∀ (hq0 : q.val.coeff 0 ≠ 0) (hpq : p ≠ q),
      tame (MilnorK.K2.DVR.data hπ)
        (polynomialNorm q
          (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq)) (rootUnit q hq0)) -
        symbol (constantCoeffUnit p hp0) (constantCoeffUnit q hq0) +
        (p.val.natDegree * q.val.natDegree) • symbol (-1 : kˣ) (-1)) = 0 ∧
      specialize (MilnorK.K2.DVR.data hπ) (MilnorK.K2.DVR.unitReductionCompatible hπ)
        (polynomialNorm q
          (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq)) (rootUnit q hq0)) -
        symbol (constantCoeffUnit p hp0) (constantCoeffUnit q hq0) +
        (p.val.natDegree * q.val.natDegree) • symbol (-1 : kˣ) (-1)) = 0)
    (b : (AdjoinRoot p.val)ˣ) :
    tame (MilnorK.K2.DVR.data hπ) (polynomialNorm p (symbol b (rootUnit p hp0))) = 0 ∧
    specialize (MilnorK.K2.DVR.data hπ) (MilnorK.K2.DVR.unitReductionCompatible hπ)
      (polynomialNorm p (symbol b (rootUnit p hp0))) = 0 := by
  exact polynomialNorm_root_mem_of_lower_degree p hp0
    ((tame (MilnorK.K2.DVR.data hπ)).ker ⊓
      (specialize (MilnorK.K2.DVR.data hπ) (MilnorK.K2.DVR.unitReductionCompatible hπ)).ker)
    hconstant hlower b

end LocalKernel

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModule := `Aglib.KTheory.MilnorK.K3.PolynomialNormRootRecurrence
  let consumerPrefix := `AglibTest.PolynomialNormRootRecurrence
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
      throwError "Root recurrence declaration {name} is absent from the kernel environment"
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} root recurrence declarations and consumers, \
    including private helpers: only standard Lean logical foundations."

end AglibTest.PolynomialNormRootRecurrence
