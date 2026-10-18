/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.FiniteComparison
public import Aglib.KTheory.MilnorK.RestrictionKernel

/-!
# Prime-normal presentation independence

The actual split-branch formula is invariant under a specified base-field
root-algebra equivalence. For a normal prime-degree root extension, restriction
therefore kills the difference of the two presentation norms. Finite classwise
mixed generation supplies a second restriction of coprime degree killing the
same difference. The proved auxiliary degree retractions detect its vanishing.

Normality is explicit. This is presentation independence for prime-normal
extensions, not general finite-extension or norm-tower independence. Milnor
degree zero is handled separately using the actual degree law and `K₀ = ℤ`.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial PolynomialResidue Polynomial.LocalResidue

variable {k L : Type*} [Field k] [Field L]

/-- Two presentation norms have the same restriction to any specified common
splitting field. The finite sums are reindexed by the actual field embeddings. -/
theorem polynomialNorm_restrict_map_algEquiv_of_splits [CharZero k] [Algebra k L]
    (n : ℕ) (p q : MonicIrreducible k) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (hp : (p.val.map (algebraMap k L)).Splits)
    (hq : (q.val.map (algebraMap k L)).Splits) (x : K (AdjoinRoot p.val) n) :
    MilnorK.map n (algebraMap k L) (polynomialNorm n q (MilnorK.map n e.toRingHom x)) =
      MilnorK.map n (algebraMap k L) (polynomialNorm n p x) := by
  classical
  let ep := Equiv.ofBijective (splitBranchAlgHom p hp)
    ⟨splitBranchAlgHom_injective p hp, splitBranchAlgHom_surjective p hp⟩
  let eq := Equiv.ofBijective (splitBranchAlgHom q hq)
    ⟨splitBranchAlgHom_injective q hq, splitBranchAlgHom_surjective q hq⟩
  let B := eq.trans ((AlgEquiv.arrowCongr e.symm (AlgEquiv.refl : L ≃ₐ[k] L)).trans ep.symm)
  have hB (r : {r // r ∈ placesAbove (algebraMap k L) q}) :
      splitBranchAlgHom p hp (B r) = (splitBranchAlgHom q hq r).comp e.toAlgHom := by
    change ep (ep.symm _) = _
    rw [ep.apply_symm_apply]
    rfl
  rw [polynomialNorm_restrict_of_splits (algebraMap k L) n q hq,
    polynomialNorm_restrict_of_splits (algebraMap k L) n p hp]
  simp only [Finset.attach_eq_univ]
  apply Fintype.sum_equiv B
  intro r
  have hmap := congrArg AlgHom.toRingHom (hB r)
  change (MilnorK.K3.PolynomialNorm.splitBranchMap (algebraMap k L) p hp (B r)) =
    (MilnorK.K3.PolynomialNorm.splitBranchMap (algebraMap k L) q hq r).comp e.toRingHom at hmap
  rw [← LinearMap.comp_apply, ← MilnorK.map_comp, ← hmap]

/-- In degree zero, the original polynomial norm is multiplication by its
actual degree under the literal integer comparison. -/
theorem zeroEquiv_polynomialNorm (p : MonicIrreducible k) (x : K (AdjoinRoot p.val) 0) :
    zeroEquiv k (polynomialNorm 0 p x) =
      (p.val.natDegree : ℤ) * zeroEquiv (AdjoinRoot p.val) x := by
  let y : K k 0 := (zeroEquiv k).symm (zeroEquiv (AdjoinRoot p.val) x)
  have hy : MilnorK.map 0 (algebraMap k (AdjoinRoot p.val)) y = x := by
    apply (zeroEquiv (AdjoinRoot p.val)).injective
    rw [zeroEquiv_map]
    exact (zeroEquiv k).apply_symm_apply _
  rw [← hy, polynomialNorm_map_constants, map_smul, zeroEquiv_map]
  rfl

/-- Degree-zero presentation independence follows from equal extension degrees
and needs no characteristic or normality assumption. -/
theorem polynomialNorm_zero_map_algEquiv (p q : MonicIrreducible k)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) (x : K (AdjoinRoot p.val) 0) :
    polynomialNorm 0 q (MilnorK.map 0 e.toRingHom x) = polynomialNorm 0 p x := by
  apply (zeroEquiv k).injective
  rw [zeroEquiv_polynomialNorm, zeroEquiv_polynomialNorm, zeroEquiv_map,
    natDegree_eq_of_root_algEquiv p q e]

/-- Explicit normality makes both algebra-equivalent presentations split in
the original root field, so their norm difference restricts to zero there. -/
theorem polynomialNorm_restrict_map_algEquiv_of_normal [CharZero k]
    (n : ℕ) (p q : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) (x : K (AdjoinRoot p.val) n) :
    MilnorK.map n (algebraMap k (AdjoinRoot p.val))
        (polynomialNorm n q (MilnorK.map n e.toRingHom x)) =
      MilnorK.map n (algebraMap k (AdjoinRoot p.val)) (polynomialNorm n p x) := by
  apply polynomialNorm_restrict_map_algEquiv_of_splits n p q e
  · have hmin : p.val = minpoly k (AdjoinRoot.root p.val) :=
      minpoly.eq_of_irreducible_of_monic p.property.2
        (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) p.property.1
    exact (congrArg (fun f : k[X] =>
      (f.map (algebraMap k (AdjoinRoot p.val))).Splits) hmin).mpr
        (Normal.splits (inferInstance : Normal k (AdjoinRoot p.val)) _)
  · have hmin : q.val = minpoly k (e.symm (AdjoinRoot.root q.val)) :=
      minpoly.eq_of_irreducible_of_monic q.property.2
        (AdjoinRoot.aeval_algHom_eq_zero q.val e.symm.toAlgHom) q.property.1
    exact (congrArg (fun f : k[X] =>
      (f.map (algebraMap k (AdjoinRoot p.val))).Splits) hmin).mpr
        (Normal.splits (inferInstance : Normal k (AdjoinRoot p.val)) _)

/-- In a normal prime-degree extension, every actual polynomial-presentation
norm is independent of the specified primitive-element presentation, in all
Milnor degrees. The proof uses two genuine finite separable restrictions of
coprime degrees and their already-constructed auxiliary degree retractions. -/
theorem polynomialNorm_map_algEquiv_of_prime_normal [CharZero k]
    (n : ℕ) (p q : MonicIrreducible k) (hp : p.val.natDegree.Prime)
    [Normal k (AdjoinRoot p.val)] (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (x : K (AdjoinRoot p.val) n) :
    polynomialNorm n q (MilnorK.map n e.toRingHom x) = polynomialNorm n p x := by
  cases n with
  | zero => exact polynomialNorm_zero_map_algEquiv p q e x
  | succ m =>
    obtain ⟨L, hL, hA, hfd, hsep, hcop, hLmap⟩ :=
      exists_coprime_restriction_eq_of_algEquiv p q hp e m x
    let := hfd
    let := hsep
    let : FiniteDimensional k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
    have hcop' : (Module.finrank k (AdjoinRoot p.val)).Coprime (Module.finrank k L) := by
      rwa [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    apply sub_eq_zero.mp
    apply eq_zero_of_two_maps_eq_zero_of_coprime k (AdjoinRoot p.val) L hcop' (m + 1)
    · rw [map_sub, polynomialNorm_restrict_map_algEquiv_of_normal, sub_self]
    · rw [map_sub, hLmap, sub_self]

end MilnorK.PolynomialNorm
