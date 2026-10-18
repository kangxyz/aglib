/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootNormEvaluation
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Determinant norms and resultants in a simple field extension

For a monic irreducible polynomial in characteristic zero, the actual algebra
norm of a polynomial evaluated at the distinguished root equals its resultant.
Swapping the two polynomials gives the signed norm reciprocity identity.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k : Type*} [Field k] [CharZero k]

/-- The determinant norm in the field quotient is the polynomial resultant.
The second polynomial is arbitrary, including zero and constants. -/
theorem norm_mk_eq_resultant (p q : k[X]) (hp : p.Monic) [Fact (Irreducible p)] :
    Algebra.norm k (mk p q) = Polynomial.resultant p q := by
  classical
  let E := AlgebraicClosure k
  let : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  apply (algebraMap k E).injective
  have hnorm : algebraMap k E (Algebra.norm k (mk p q)) =
      ((p.aroots E).map (fun x => aeval x q)).prod := by
    rw [Algebra.norm_eq_prod_embeddings k E]
    rw [Fintype.prod_equiv (AdjoinRoot.equiv E k p hp.ne_zero)
      (fun σ => σ (mk p q)) (fun x => aeval (x : E) q)]
    · rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod,
        Multiset.toFinset_val, Multiset.dedup_eq_self.mpr]
      · exact nodup_roots ((Fact.out : Irreducible p).separable.map)
      · intro x; rfl
    · intro σ
      rw [← aeval_eq, ← aeval_algHom_apply]
      rfl
  rw [hnorm]
  have hres := Polynomial.resultant_eq_prod_eval
    (p.map (algebraMap k E)) (q.map (algebraMap k E)) q.natDegree
    (natDegree_map_le) (IsAlgClosed.splits _)
  simpa only [natDegree_map, resultant_map_map, (hp.map (algebraMap k E)).leadingCoeff,
    one_pow, one_mul, eval_map_algebraMap, aroots_def] using hres.symm

/-- Interchanging two monic irreducibles changes the norm of their evaluations
by exactly the usual degree-product sign. Distinctness is not needed here. -/
theorem norm_mk_reciprocity (p q : k[X]) (hp : p.Monic) (hq : q.Monic)
    [Fact (Irreducible p)] [Fact (Irreducible q)] :
    Algebra.norm k (mk p q) = (-1) ^ (p.natDegree * q.natDegree) *
      Algebra.norm k (mk q p) := by
  rw [norm_mk_eq_resultant p q hp, norm_mk_eq_resultant q p hq]
  exact Polynomial.resultant_comm p q p.natDegree q.natDegree

end AdjoinRoot
