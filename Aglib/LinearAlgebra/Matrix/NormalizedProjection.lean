/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.Matrix.GenericProjection
public import Aglib.RingTheory.FittingIdeal.Minors
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Primitive generic determinants normalized by an actual generating minor

The quotient polynomial is constructed from determinant multilinearity and the
actual ideal of minors. A chosen generating minor supplies an evaluation equal
to one, so the quotient polynomial remains nonzero over the residue field.
-/

@[expose] public noncomputable section

open MvPolynomial IsLocalRing

namespace Matrix

variable {S ι : Type*} [CommRing S] [IsDomain S] [IsLocalRing S]
variable [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- Dividing the generic determinant by a nonzero generating minor gives an
actual polynomial whose coordinate-selection value is one and whose residue is nonzero. -/
theorem exists_normalized_genericProjection (A : Matrix (Fin r) ι S) (δ : S)
    (hδ : δ ≠ 0) (hI : A.minorIdeal r = Ideal.span {δ})
    (c₀ : Fin r → ι) (hc₀ : (A.submatrix id c₀).det = δ) :
    ∃ H : MvPolynomial (Fin r × ι) S,
      (genericProjection A).det = C δ * H ∧
      eval (fun q : Fin r × ι => if q.2 = c₀ q.1 then 1 else 0) H = 1 ∧
      MvPolynomial.map (residue S) H ≠ 0 := by
  classical
  let P := MvPolynomial (Fin r × ι) S
  let V : ι → Fin r → P := fun l i => C (A i l)
  let D : MultilinearMap P (fun _ : Fin r => Fin r → P) P :=
    (detRowAlternating : (Fin r → P) [⋀^Fin r]→ₗ[P] P).toMultilinearMap
  have hrows : ∀ j, (genericProjection A)ᵀ j ∈ Submodule.span P (Set.range V) := by
    intro j
    have hm : (∑ l, X (j, l) • V l) ∈ Submodule.span P (Set.range V) :=
      Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    convert hm using 1
    funext i
    simp only [genericProjection, transpose_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, V, mul_comm]
  have hm := D.map_mem_span_of_forall_mem_span hrows
  have hpoly : (genericProjection A).det ∈ (Ideal.span {C δ} : Ideal P) := by
    change ((genericProjection A)ᵀ).det ∈ _ at hm
    rw [det_transpose] at hm
    apply (Submodule.span_le.mpr ?_) hm
    rintro _ ⟨w, hw, rfl⟩
    choose c hc using hw
    have hmem : (A.submatrix id c).det ∈ Ideal.span {δ} := by
      rw [← hI]
      exact Ideal.subset_span ⟨id, c, rfl⟩
    have hmap := Ideal.mem_map_of_mem (C : S →+* P) hmem
    rw [Ideal.map_span, Set.image_singleton] at hmap
    have he : w = ((A.submatrix id c).map (C : S →+* P))ᵀ := by
      funext j i
      exact (congrFun (hc j) i).symm
    have hd := (C : S →+* P).map_det (A.submatrix id c)
    change C (A.submatrix id c).det = ((A.submatrix id c).map (C : S →+* P)).det at hd
    change Matrix.det w ∈ _
    rw [he, det_transpose, ← hd]
    exact hmap
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp hpoly
  let v : Fin r × ι → S := fun q => if q.2 = c₀ q.1 then 1 else 0
  have hev : eval v H = 1 := by
    have hh := congrArg (eval v) hH
    rw [eval_genericProjection_det, hc₀, map_mul, eval_C] at hh
    apply mul_left_cancel₀ hδ
    rw [mul_one]
    exact hh.symm
  refine ⟨H, hH, hev, ?_⟩
  intro hz
  have hh := MvPolynomial.map_eval (residue S) v H
  rw [hev, map_one, hz, map_zero] at hh
  exact one_ne_zero hh

end Matrix
