/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Irreducibility under coprime finite coefficient extensions

A monic irreducible polynomial remains irreducible over a finite extension
whose degree is coprime to its degree. The proof uses the actual minimal
polynomial of a root of a factor and finite tower degrees. No separability,
perfectness, or assumed linear disjointness is needed.
-/

@[expose] public noncomputable section

namespace Polynomial

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]

/-- A factor over the larger field retains a degree divisible by the original
irreducible degree when the coefficient-extension degree is coprime to it. -/
theorem natDegree_dvd_of_irreducible_factor_of_coprime {p : k[X]}
    (hp : p.Monic) (hirr : Irreducible p)
    (hcop : p.natDegree.Coprime (Module.finrank k L))
    {q : L[X]} (hq : Irreducible q) (hdiv : q ∣ p.map (algebraMap k L)) :
    p.natDegree ∣ q.natDegree := by
  let : Fact (Irreducible q) := ⟨hq⟩
  let : FiniteDimensional L (AdjoinRoot q) := (AdjoinRoot.powerBasis hq.ne_zero).finite
  let : FiniteDimensional k (AdjoinRoot q) := Module.Finite.trans L (AdjoinRoot q)
  have hroot : aeval (AdjoinRoot.root q) p = 0 := by
    rw [← aeval_map_algebraMap L]
    exact eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hdiv (AdjoinRoot.eval₂_root q)
  have hmin : p = minpoly k (AdjoinRoot.root q) :=
    minpoly.eq_of_irreducible_of_monic hirr hroot hp
  have hdvd : p.natDegree ∣ Module.finrank k L * q.natDegree := by
    rw [← AdjoinRoot.powerBasis_dim hq.ne_zero,
      ← (AdjoinRoot.powerBasis hq.ne_zero).finrank, Module.finrank_mul_finrank, hmin]
    exact minpoly.degree_dvd (IsIntegral.of_finite k (AdjoinRoot.root q))
  exact hcop.dvd_of_dvd_mul_left hdvd

/-- Irreducibility survives a finite coefficient extension of coprime degree.
The finite extension need not be separable. -/
theorem Monic.irreducible_map_of_natDegree_coprime {p : k[X]}
    (hp : p.Monic) (hirr : Irreducible p)
    (hcop : p.natDegree.Coprime (Module.finrank k L)) :
    Irreducible (p.map (algebraMap k L)) := by
  have hne : p.map (algebraMap k L) ≠ 0 := Polynomial.map_ne_zero hp.ne_zero
  have hunit : ¬ IsUnit (p.map (algebraMap k L)) := by
    intro h
    have hd := natDegree_eq_zero_of_isUnit h
    rw [Polynomial.natDegree_map] at hd
    exact (ne_of_gt hirr.natDegree_pos) hd
  obtain ⟨q, hq, hdiv⟩ := WfDvdMonoid.exists_irreducible_factor hunit hne
  have hle : p.natDegree ≤ q.natDegree :=
    Nat.le_of_dvd hq.natDegree_pos
      (natDegree_dvd_of_irreducible_factor_of_coprime hp hirr hcop hq hdiv)
  exact (associated_of_dvd_of_natDegree_le hdiv hne
    (by simpa only [Polynomial.natDegree_map] using hle)).irreducible hq

end Polynomial
