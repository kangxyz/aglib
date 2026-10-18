/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# Normality of a literal scalar-extension branch

Every irreducible branch of a normal root extension is normal over the new
coefficient field. The branch root generates a splitting field of the original
coefficient-image polynomial. No separability, finite coefficient extension,
prime degree or norm law is needed.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
  {p : k[X]} {q : L[X]} [Fact (Irreducible p)] [Fact (Irreducible q)]
  [Normal k (AdjoinRoot p)]

/-- An actual irreducible factor after scalar extension has a normal root field. -/
theorem normal_of_dvd_map (hp : p.Monic) (hd : q ∣ p.map (algebraMap k L)) :
    Normal L (AdjoinRoot q) := by
  have hroot : aeval (root q) p = 0 := by
    rw [← aeval_map_algebraMap L]
    exact eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hd (eval₂_root q)
  let e : AdjoinRoot p →ₐ[k] AdjoinRoot q :=
    liftAlgHom p (Algebra.ofId k (AdjoinRoot q)) (root q) hroot
  let : Algebra (AdjoinRoot p) (AdjoinRoot q) := e.toRingHom.toAlgebra
  let : IsScalarTower k (AdjoinRoot p) (AdjoinRoot q) :=
    IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  have hsplit : (p.map (algebraMap k (AdjoinRoot q))).Splits := by
    have hs := Normal.splits (inferInstance : Normal k (AdjoinRoot p)) (root p)
    rw [minpoly_root (Fact.out : Irreducible p).ne_zero, hp.leadingCoeff,
      inv_one, C_1, mul_one] at hs
    simpa only [map_map, ← IsScalarTower.algebraMap_eq] using
      hs.map (algebraMap (AdjoinRoot p) (AdjoinRoot q))
  have hsL : ((p.map (algebraMap k L)).map (algebraMap L (AdjoinRoot q))).Splits := by
    simpa only [map_map, ← IsScalarTower.algebraMap_eq] using hsplit
  let : IsSplittingField L (AdjoinRoot q) (p.map (algebraMap k L)) := ⟨hsL, by
    apply top_unique
    rw [← adjoinRoot_eq_top (f := q)]
    apply Algebra.adjoin_mono
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact mem_rootSet.mpr ⟨map_ne_zero hp.ne_zero, by rwa [aeval_map_algebraMap]⟩⟩
  exact Normal.of_isSplittingField (p.map (algebraMap k L))

end AdjoinRoot
