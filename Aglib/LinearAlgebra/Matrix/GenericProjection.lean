/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.Multilinear.Span
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Nonzero generic projection determinants from actual spanning columns

The full-row minor is produced by determinant multilinearity on spans. No rank
or nonzero-minor hypothesis is substituted for the spanning hypothesis.
-/

@[expose] public noncomputable section

namespace Matrix

variable {K ι : Type*} [CommRing K] {d : ℕ}

/-- Spanning columns contain a square full-row minor with nonzero determinant. -/
theorem exists_fullRow_minor_ne_zero_of_span_eq_top [Nontrivial K] (A : Matrix (Fin d) ι K)
    (hA : Submodule.span K (Set.range Aᵀ) = ⊤) :
    ∃ c : Fin d → ι, (A.submatrix id c).det ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let D : MultilinearMap K (fun _ : Fin d => Fin d → K) K :=
    (detRowAlternating : (Fin d → K) [⋀^Fin d]→ₗ[K] K).toMultilinearMap
  have hone := D.map_mem_span_of_forall_mem_span
    (v := (1 : Matrix (Fin d) (Fin d) K)) (T := Set.range Aᵀ)
    (fun i => by rw [hA]; exact Submodule.mem_top)
  have hbot : Submodule.span K {x | ∃ w : Fin d → Fin d → K,
      (∀ i, w i ∈ Set.range Aᵀ) ∧ D w = x} = ⊥ := by
    apply Submodule.span_eq_bot.mpr
    rintro _ ⟨w, hw, rfl⟩
    choose c hc using hw
    have he : w = (A.submatrix id c)ᵀ := by
      funext j i
      exact (congrFun (hc j) i).symm
    change Matrix.det w = 0
    rw [he, det_transpose]
    exact h c
  rw [hbot] at hone
  change (1 : Matrix (Fin d) (Fin d) K).det = 0 at hone
  exact one_ne_zero (by simpa only [det_one] using hone)

variable [Fintype ι]

/-- The matrix of generic linear combinations of the original columns. -/
def genericProjection (A : Matrix (Fin d) ι K) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × ι) K) :=
  fun i j => ∑ l, MvPolynomial.C (A i l) * MvPolynomial.X (j, l)

/-- Coordinate-selection specialization recovers the actual full-row minor. -/
theorem eval_genericProjection_det [DecidableEq ι]
    (A : Matrix (Fin d) ι K) (c : Fin d → ι) :
    MvPolynomial.eval (fun q : Fin d × ι => if q.2 = c q.1 then 1 else 0)
      (genericProjection A).det = (A.submatrix id c).det := by
  classical
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [genericProjection, submatrix_apply]

/-- Spanning columns make the generic full-row determinant a nonzero polynomial. -/
theorem genericProjection_det_ne_zero [Nontrivial K] (A : Matrix (Fin d) ι K)
    (hA : Submodule.span K (Set.range Aᵀ) = ⊤) :
    (genericProjection A).det ≠ 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_fullRow_minor_ne_zero_of_span_eq_top A hA
  intro h
  have he := eval_genericProjection_det A c
  rw [h, map_zero] at he
  exact hc he.symm

end Matrix
