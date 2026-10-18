/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.Branches
public import Aglib.KTheory.MilnorK.Norm.Polynomial.PrimeNormal

/-!
# The nonnormal prime-degree presentation-independence induction step

The induction hypothesis is explicitly presentation independence for every
smaller polynomial degree over the original root field. Actual scalar branches
are matched by their quotient-field equivalences, and all have smaller degree.
This proves equality after root-field restriction, hence degree annihilation
of the difference. The existing finite coprime mixed restriction then proves
the prime-degree step without normality. This file does not claim that the
strong induction, its composite-degree cases, or a norm tower law are complete.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue AdjoinRoot

variable {k L : Type*} [Field k] [Field L]

/-- The finite indexing set in the actual norm base-change formula is exactly
the family of irreducible branches of the whole coefficient-image algebra. -/
def placesAboveBranchEquiv (φ : k →+* L) (p : MonicIrreducible k) :
    {r // r ∈ placesAbove φ p} ≃ IrreducibleBranch (p.val.map φ) where
  toFun r := ⟨r.val, (mem_placesAbove φ p r.val).mp r.property⟩
  invFun r := ⟨r.val, (mem_placesAbove φ p r.val).mpr r.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Under the stated lower-degree induction hypothesis, restriction to any
field containing the original root field compares the two presentation norms.
The hypothesis concerns actual polynomial norms of strictly smaller degree. -/
theorem polynomialNorm_restrict_map_algEquiv_of_lower_degrees
    [CharZero k] [Algebra k L]
    (n : ℕ) (p q : MonicIrreducible k) (hp : 1 < p.val.natDegree)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (f : AdjoinRoot p.val →ₐ[k] L)
    (ih : ∀ (r s : MonicIrreducible L), r.val.natDegree < p.val.natDegree →
      ∀ (ε : AdjoinRoot r.val ≃ₐ[L] AdjoinRoot s.val) (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (MilnorK.map n ε.toRingHom y) = polynomialNorm n r y)
    (x : K (AdjoinRoot p.val) n) :
    MilnorK.map n (algebraMap k L)
        (polynomialNorm n q (MilnorK.map n e.toRingHom x)) =
      MilnorK.map n (algebraMap k L) (polynomialNorm n p x) := by
  classical
  let φ := algebraMap k L
  let hp' : p.val.map φ ≠ 0 := Polynomial.map_ne_zero p.property.2.ne_zero
  let hq' : q.val.map φ ≠ 0 := Polynomial.map_ne_zero q.property.2.ne_zero
  let E := coefficientEquiv (L := L) e
  let B := (placesAboveBranchEquiv φ p).trans
    ((polynomialBranchEquiv _ _ hp' hq' E).trans (placesAboveBranchEquiv φ q).symm)
  rw [polynomialNorm_restrict, polynomialNorm_restrict]
  simp only [Finset.attach_eq_univ]
  symm
  apply Fintype.sum_equiv B
  intro r
  let rb : IrreducibleBranch (p.val.map φ) := placesAboveBranchEquiv φ p r
  let ε : AdjoinRoot r.val.val ≃ₐ[L] AdjoinRoot (B r).val.val :=
    polynomialBranchAlgEquiv _ _ hp' hq' E rb
  have hdeg : r.val.val.natDegree < p.val.natDegree :=
    scalarBranch_natDegree_lt_of_rootHom p.val p.property.1 hp f rb
  have hsquare : ε.toRingHom.comp
      (adjoinRootMap φ p.val r.val.val ((mem_placesAbove φ p r.val).mp r.property)) =
      (adjoinRootMap φ q.val (B r).val.val
        ((mem_placesAbove φ q (B r).val).mp (B r).property)).comp e.toRingHom := by
    apply RingHom.ext
    intro a
    exact scalarBranchAlgEquiv_adjoinRootMap p.val q.val e rb a
  have hmaps : MilnorK.map n ε.toRingHom
      (MilnorK.map n
        (adjoinRootMap φ p.val r.val.val ((mem_placesAbove φ p r.val).mp r.property)) x) =
      MilnorK.map n (adjoinRootMap φ q.val (B r).val.val
        ((mem_placesAbove φ q (B r).val).mp (B r).property))
          (MilnorK.map n e.toRingHom x) := by
    simpa only [MilnorK.map_comp, LinearMap.comp_apply] using
      congrArg (fun g => MilnorK.map n g x) hsquare
  exact (ih r.val (B r).val hdeg ε _).symm.trans
    (congrArg (polynomialNorm n (B r).val) hmaps)

/-- Restriction to the original root field kills the norm difference under
strictly smaller-degree presentation independence; normality is not required. -/
theorem polynomialNorm_restrict_root_of_lower_degrees [CharZero k]
    (n : ℕ) (p q : MonicIrreducible k) (hp : 1 < p.val.natDegree)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (ih : ∀ (r s : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < p.val.natDegree →
      ∀ (ε : AdjoinRoot r.val ≃ₐ[AdjoinRoot p.val] AdjoinRoot s.val)
        (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (MilnorK.map n ε.toRingHom y) = polynomialNorm n r y)
    (x : K (AdjoinRoot p.val) n) :
    MilnorK.map n (algebraMap k (AdjoinRoot p.val))
        (polynomialNorm n q (MilnorK.map n e.toRingHom x)) =
      MilnorK.map n (algebraMap k (AdjoinRoot p.val)) (polynomialNorm n p x) :=
  polynomialNorm_restrict_map_algEquiv_of_lower_degrees n p q hp e
    (AlgHom.id k (AdjoinRoot p.val)) ih x

/-- The original extension degree annihilates the difference, using the
proved auxiliary degree retraction rather than a presumed canonical norm. -/
theorem polynomialNorm_degree_smul_sub_eq_zero_of_lower_degrees [CharZero k]
    (n : ℕ) (p q : MonicIrreducible k) (hp : 1 < p.val.natDegree)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (ih : ∀ (r s : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < p.val.natDegree →
      ∀ (ε : AdjoinRoot r.val ≃ₐ[AdjoinRoot p.val] AdjoinRoot s.val)
        (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (MilnorK.map n ε.toRingHom y) = polynomialNorm n r y)
    (x : K (AdjoinRoot p.val) n) :
    (p.val.natDegree : ℤ) •
      (polynomialNorm n q (MilnorK.map n e.toRingHom x) - polynomialNorm n p x) = 0 := by
  let : FiniteDimensional k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
  have h := finrank_smul_eq_zero_of_map_eq_zero k (AdjoinRoot p.val) n
    (polynomialNorm n q (MilnorK.map n e.toRingHom x) - polynomialNorm n p x)
    (by rw [map_sub, polynomialNorm_restrict_root_of_lower_degrees n p q hp e ih x,
      sub_self])
  simpa only [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim] using h

/-- The genuine prime-degree strong-induction step. Its smaller-degree
hypothesis is explicit, and no normality or norm tower law is supplied. -/
theorem polynomialNorm_map_algEquiv_of_prime_of_lower_degrees [CharZero k]
    (n : ℕ) (p q : MonicIrreducible k) (hp : p.val.natDegree.Prime)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (ih : ∀ (r s : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < p.val.natDegree →
      ∀ (ε : AdjoinRoot r.val ≃ₐ[AdjoinRoot p.val] AdjoinRoot s.val)
        (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (MilnorK.map n ε.toRingHom y) = polynomialNorm n r y)
    (x : K (AdjoinRoot p.val) n) :
    polynomialNorm n q (MilnorK.map n e.toRingHom x) = polynomialNorm n p x := by
  cases n with
  | zero => exact polynomialNorm_zero_map_algEquiv p q e x
  | succ m =>
    obtain ⟨L, hL, hA, hfd, hsep, hcop, hrestricted⟩ :=
      exists_coprime_restriction_eq_of_algEquiv p q hp e m x
    let := hfd
    let := hsep
    exact eq_of_map_eq_of_coprime k L (m + 1) p.val.natDegree hcop _ _ hrestricted
      (polynomialNorm_degree_smul_sub_eq_zero_of_lower_degrees
        (m + 1) p q hp.one_lt e ih x)

end MilnorK.PolynomialNorm
