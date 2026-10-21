/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.Matrix.GenericProjection
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.Rename

/-! # Separating determinants in the whole generic coordinate matrix

The selected new coordinates use rows of the same whole matrix whose adjugate
controls retained Jacobian minors. Renaming variables is injective, so the
actual spanning-columns hypothesis produces a nonzero condition in this common
polynomial ring.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Matrix

variable {K n : Type*} [CommRing K] [Fintype n] {d : ℕ}

/-- Renaming the projection variables embeds the separating determinant into
rows of the whole generic coordinate matrix. -/
theorem rename_genericProjection_det (A : Matrix (Fin d) n K) (e : Fin d ↪ n) :
    rename (fun q : Fin d × n => (e q.1, q.2)) (genericProjection A).det =
      ((A.map (C : K →+* MvPolynomial (n × n) K) *
        (mvPolynomialX n n K).transpose).submatrix id e).det := by
  classical
  rw [AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change rename (fun q : Fin d × n => (e q.1, q.2))
    (∑ l, C (A i l) * X (j, l)) = ∑ l, C (A i l) * X (e j, l)
  simp only [map_sum, map_mul, rename_C, rename_X]

/-- Spanning differential-coordinate columns give a nonzero separating
condition in the same whole generic coordinate matrix. -/
theorem whole_genericProjection_det_ne_zero [Nontrivial K]
    (A : Matrix (Fin d) n K) (e : Fin d ↪ n)
    (hA : Submodule.span K (Set.range A.transpose) = ⊤) :
    ((A.map (C : K →+* MvPolynomial (n × n) K) *
      (mvPolynomialX n n K).transpose).submatrix id e).det ≠ 0 := by
  classical
  have hi : Function.Injective (fun q : Fin d × n => (e q.1, q.2)) := by
    intro a b h
    apply Prod.ext
    · exact e.injective (congrArg (fun q : n × n => q.1) h)
    · exact congrArg (fun q : n × n => q.2) h
  rw [← rename_genericProjection_det]
  intro h
  apply genericProjection_det_ne_zero A hA
  exact rename_injective _ hi (h.trans (map_zero _).symm)

end Matrix
