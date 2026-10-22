/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.Matrix.NormalizedProjection
public import Mathlib.Logic.Equiv.Fintype

/-! # Retaining a generating minor under the same generic coordinate matrix

The polynomial condition uses the adjugate of the native whole generic matrix.
A permutation extending the actual selected columns gives a unit specialization
of the normalized condition. No independent inverse-coordinate matrix is chosen.
-/

@[expose] public noncomputable section

open MvPolynomial IsLocalRing

namespace Matrix

variable {S n : Type*} [CommRing S] [IsDomain S] [IsLocalRing S]
variable [Fintype n] [DecidableEq n] {r : ℕ}

omit [IsDomain S] [IsLocalRing S] in
private theorem eval_retained_adjugate (A : Matrix (Fin r) n S)
    (b : Fin r → n) (T : Matrix n n S) :
    eval (fun q : n × n => T q.1 q.2)
      (((A.map (C : S →+* MvPolynomial (n × n) S)) *
        (mvPolynomialX n n S).adjugate).submatrix id b).det =
      ((A * T.adjugate).submatrix id b).det := by
  let E := eval (fun q : n × n => T q.1 q.2)
  have ha : E.mapMatrix (mvPolynomialX n n S).adjugate = T.adjugate := by
    rw [RingHom.map_adjugate, mvPolynomialX_mapMatrix_eval]
  rw [RingHom.map_det]
  congr 1
  ext i j
  change E (∑ l, C (A i l) * (mvPolynomialX n n S).adjugate l (b j)) =
    ∑ l, A i l * T.adjugate l (b j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_mul, eval_C]
  congr 1
  exact congrFun (congrFun ha l) (b j)

/-- The normalized retained minor for the adjugate of the whole generic matrix
is an actual polynomial nonzero modulo the maximal ideal. -/
theorem exists_normalized_retained_adjugate (A : Matrix (Fin r) n S) (δ : S)
    (hδ : δ ≠ 0) (hI : A.minorIdeal r = Ideal.span {δ})
    (c₀ : Fin r → n) (hc₀ : (A.submatrix id c₀).det = δ) (b : Fin r ↪ n) :
    ∃ H : MvPolynomial (n × n) S,
      (((A.map (C : S →+* MvPolynomial (n × n) S)) *
        (mvPolynomialX n n S).adjugate).submatrix id b).det = C δ * H ∧
      MvPolynomial.map (residue S) H ≠ 0 := by
  classical
  obtain ⟨H₀, hH₀, _, _⟩ := exists_normalized_genericProjection A δ hδ hI c₀ hc₀
  let U := mvPolynomialX n n S
  let φ : MvPolynomial (Fin r × n) S →ₐ[S] MvPolynomial (n × n) S :=
    aeval (fun q => U.adjugate q.2 (b q.1))
  let H := φ H₀
  have hφ : φ.mapMatrix (genericProjection A) = (A.map C * U.adjugate).submatrix id b := by
    apply Matrix.ext
    intro i j
    change φ (∑ l, C (A i l) * X (j, l)) = ∑ l, C (A i l) * U.adjugate l (b j)
    simp only [map_sum, map_mul, φ, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
  have hH : ((A.map C * U.adjugate).submatrix id b).det = C δ * H := by
    have hh := congrArg φ hH₀
    rw [AlgHom.map_det, map_mul] at hh
    rw [hφ] at hh
    change ((A.map C * U.adjugate).submatrix id b).det = φ (C δ) * φ H₀ at hh
    simpa only [H, φ, aeval_C, MvPolynomial.algebraMap_eq] using hh
  have hc : Function.Injective c₀ := by
    intro i j hij
    by_contra hne
    apply hδ
    exact hc₀.symm.trans (det_zero_of_column_eq hne (fun l => congrArg (A l) hij))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair c₀ b hc b.injective
  let T : Matrix n n S := (1 : Matrix n n S).submatrix σ.symm id
  let V : Matrix n n S := (1 : Matrix n n S).submatrix σ id
  have hTV : T * V = 1 := by
    rw [show V = (1 : Matrix n n S).submatrix σ id from rfl, mul_submatrix_one]
    ext i j
    simp [T, submatrix_apply, one_apply]
  have hu : IsUnit T.det := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨V.det, ?_⟩
    rw [← det_mul, hTV, det_one]
  have hAV : (A * V).submatrix id b = A.submatrix id c₀ := by
    rw [show V = (1 : Matrix n n S).submatrix σ id from rfl, mul_submatrix_one]
    ext i j
    change A i (σ.symm (b j)) = A i (c₀ j)
    rw [← hσ j, Equiv.symm_apply_apply]
  have hadj : T.adjugate = T.det • V := by
    calc
      T.adjugate = T.adjugate * (T * V) := by rw [hTV, mul_one]
      _ = (T.adjugate * T) * V := (mul_assoc _ _ _).symm
      _ = (T.det • (1 : Matrix n n S)) * V := by rw [adjugate_mul]
      _ = T.det • V := by rw [smul_mul_assoc, one_mul]
  have hdet : ((A * T.adjugate).submatrix id b).det = T.det ^ r * δ := by
    rw [hadj, Matrix.mul_smul]
    change (T.det • (A * V).submatrix id b).det = _
    rw [det_smul, Fintype.card_fin, hAV, hc₀]
  let E := eval (fun q : n × n => T q.1 q.2)
  have heH : E H = T.det ^ r := by
    have hh := congrArg E hH
    rw [eval_retained_adjugate, hdet, map_mul, eval_C] at hh
    apply mul_left_cancel₀ hδ
    exact hh.symm.trans (mul_comm _ _)
  refine ⟨H, hH, ?_⟩
  intro hz
  have hh := MvPolynomial.map_eval (residue S) (fun q : n × n => T q.1 q.2) H
  rw [heH, hz, map_zero] at hh
  exact ((hu.pow r).map (residue S)).ne_zero hh

end Matrix
