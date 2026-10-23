/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Tsen.AlgebraicallyClosed
public import Aglib.FieldTheory.Tsen.Coefficients
public import Aglib.FieldTheory.Tsen.PolynomialDegree
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Polynomial solutions of homogeneous systems

A finite system of degree-`d` forms over `K[T]`, with more than `d` times as
many variables as equations, has a nonzero polynomial solution when `K` is
algebraically closed. The proof expands a bounded-degree polynomial ansatz and
applies the common-zero theorem to its scalar coefficients.
-/

@[expose] public section

open scoped Polynomial

namespace MvPolynomial

/-- The homogeneous common-zero theorem with arbitrary finite variable indices. -/
theorem exists_ne_zero_common_zero_homogeneous_finite {K ι σ : Type*}
    [Field K] [IsAlgClosed K] [Fintype ι] [Fintype σ]
    (p : ι → MvPolynomial σ K) (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hcard : Fintype.card ι < Fintype.card σ) :
    ∃ x : σ → K, x ≠ 0 ∧ ∀ i, eval x (p i) = 0 := by
  let e := Fintype.equivFin σ
  obtain ⟨x, hx, hpx⟩ := exists_ne_zero_common_zero_homogeneous
    (fun i => rename e (p i)) d hd (fun i => (hp i).rename_isHomogeneous) hcard
  refine ⟨x ∘ e, ?_, ?_⟩
  · intro h
    apply hx
    funext j
    simpa using congrFun h (e.symm j)
  · intro i
    simpa only [eval_rename] using hpx i

private noncomputable def polynomialAnsatz {K σ : Type*} [Field K] (m : ℕ) (i : σ) :
    MvPolynomial (σ × Fin (m + 1)) K[X] :=
  ∑ j : Fin (m + 1), C (Polynomial.X ^ (j : ℕ)) * X (i, j)

private theorem polynomialAnsatz_homogeneous {K σ : Type*} [Field K] (m : ℕ) (i : σ) :
    (polynomialAnsatz (K := K) m i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_X _ _).C_mul _

open Classical in
private theorem eval_polynomialAnsatz {K σ : Type*} [Field K] (m : ℕ)
    (a : σ × Fin (m + 1) → K) (i : σ) :
    eval (fun j => Polynomial.C (a j)) (polynomialAnsatz m i) =
      Polynomial.ofFn (m + 1) (fun j => a (i, j)) := by
  simp only [polynomialAnsatz, map_sum, eval_mul, eval_C, eval_X,
    Polynomial.ofFn_eq_sum_monomial]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm, Polynomial.C_mul_X_pow_eq_monomial]

open Classical in
/-- Homogeneous polynomial equations have a nonzero polynomial solution when
there are more than degree times as many variables as equations. -/
theorem exists_polynomial_solution {K ι σ : Type*} [Field K] [IsAlgClosed K]
    [Fintype ι] [Fintype σ] (p : ι → MvPolynomial σ K[X]) {d : ℕ} (hd : 0 < d)
    (hp : ∀ i, (p i).IsHomogeneous d)
    (hcard : Fintype.card ι * d < Fintype.card σ) :
    ∃ x : σ → K[X], x ≠ 0 ∧ ∀ i, eval x (p i) = 0 := by
  let D := Finset.univ.sup fun i => (p i).support.sup fun e => ((p i).coeff e).natDegree
  have hD : ∀ i e, e ∈ (p i).support → ((p i).coeff e).natDegree ≤ D := by
    intro i e he
    exact (Finset.le_sup (f := fun e => ((p i).coeff e).natDegree) he).trans
      (Finset.le_sup (f := fun j => (p j).support.sup
        fun e => ((p j).coeff e).natDegree) (Finset.mem_univ i))
  let m := Fintype.card ι * (D + 1)
  let Q : ι → MvPolynomial (σ × Fin (m + 1)) K[X] :=
    fun i => eval₂ C (polynomialAnsatz m) (p i)
  have hQ : ∀ i, (Q i).IsHomogeneous d := by
    intro i
    simpa only [one_mul] using (hp i).eval₂ C (polynomialAnsatz m)
      (fun _ => isHomogeneous_C _ _) (polynomialAnsatz_homogeneous m)
  let F : (ι × Fin (D + d * m + 1)) → MvPolynomial (σ × Fin (m + 1)) K :=
    fun j => AddMonoidAlgebra.map (Polynomial.lcoeff K j.2).toAddMonoidHom (Q j.1)
  have hF : ∀ j, (F j).IsHomogeneous d := fun j => (hQ j.1).map_addHom _
  have hcount : Fintype.card (ι × Fin (D + d * m + 1)) <
      Fintype.card (σ × Fin (m + 1)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have hmul := Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr hcard)
    dsimp [m] at *
    nlinarith
  obtain ⟨a, ha, hFa⟩ := exists_ne_zero_common_zero_homogeneous_finite F
    (fun _ => d) (fun _ => hd) hF hcount
  let x : σ → K[X] := fun i => Polynomial.ofFn (m + 1) (fun j => a (i, j))
  have heval : ∀ i, eval (fun j => Polynomial.C (a j)) (Q i) = eval x (p i) := by
    intro i
    dsimp only [Q]
    rw [eval_eval₂]
    have hc : (eval (fun j => Polynomial.C (a j))).comp C = RingHom.id K[X] := by
      apply RingHom.ext
      intro r
      simp only [RingHom.comp_apply, eval_C, RingHom.id_apply]
    rw [hc, eval₂_id]
    have hx : (fun j => eval (fun z => Polynomial.C (a z))
        (polynomialAnsatz m j)) = x := funext (eval_polynomialAnsatz m a)
    rw [hx]
  refine ⟨x, ?_, ?_⟩
  · intro hx
    apply ha
    funext j
    have hj := congrFun hx j.1
    have hz : (fun t => a (j.1, t)) = 0 := by
      apply Polynomial.injective_ofFn (m + 1)
      simpa only [x, Pi.zero_apply, map_zero] using hj
    exact congrFun hz j.2
  · intro i
    apply Polynomial.ext
    intro t
    by_cases ht : t < D + d * m + 1
    · have hf := hFa (i, ⟨t, ht⟩)
      have hcoord := eval_map_linearMap (Polynomial.lcoeff K t) (Q i) a
      have hcoord' : eval a (F (i, ⟨t, ht⟩)) =
          (eval (fun j => Polynomial.C (a j)) (Q i)).coeff t := by
        simpa only [F, Algebra.algebraMap_self, RingHom.id_apply, Polynomial.algebraMap_apply,
          Polynomial.lcoeff_apply] using hcoord
      rw [hcoord', heval] at hf
      simpa only [Polynomial.coeff_zero] using hf
    · rw [Polynomial.coeff_zero]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      refine ((hp i).natDegree_eval_le (D := D) (m := m) (hD i) x ?_).trans_lt ?_
      · intro j
        exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)
      · omega

end MvPolynomial
