/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.Matrix.ChangeOfGenerators
public import Aglib.LinearAlgebra.Matrix.MinorIdealRank
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Source row operations on actual polynomial relations

A dependence detected over the source residue field is lifted over the source ring.
The resulting polynomial combinations remain in the actual relation kernel, and one
row of their derivative coefficients lies in the source maximal ideal.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.Generators

variable {R B ι : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable [IsLocalRing R] [Finite ι]

/-- Vanishing source residual maximal minors produces a unit row operation on genuine
relations, with a derivative row lying in the source maximal ideal. -/
theorem exists_relation_rowReplacement (P : Generators R B ι) {r : ℕ}
    (f : Fin r → MvPolynomial ι R) (hf : ∀ i, f i ∈ P.ker) (a : ι → R)
    (hminor : ((Matrix.of fun i j => eval a (pderiv j (f i))).map
      (IsLocalRing.residue R)).minorIdeal r = ⊥) :
    ∃ (U : Matrix (Fin r) (Fin r) R) (F : Fin r → MvPolynomial ι R) (i : Fin r),
      IsUnit U ∧ (∀ j, F j = ∑ k, C (U j k) * f k) ∧
      (∀ j, F j ∈ P.ker) ∧
      ∀ j, eval a (pderiv j (F i)) ∈ IsLocalRing.maximalIdeal R := by
  classical
  let A : Matrix (Fin r) ι R := fun i j => eval a (pderiv j (f i))
  obtain ⟨b, hb, hrel⟩ :=
    Matrix.exists_row_relation_of_minorIdeal_eq_bot (A.map (IsLocalRing.residue R)) hminor
  obtain ⟨u, i, _hu, _hi, _hdet, hU, hrow⟩ :=
    Matrix.exists_unit_rowReplacement_of_residue_relation A b hb hrel
  let U := (1 : Matrix (Fin r) (Fin r) R).updateRow i u
  let F : Fin r → MvPolynomial ι R := fun j => ∑ k, C (U j k) * f k
  refine ⟨U, F, i, hU, (fun _ => rfl), ?_, ?_⟩
  · intro j
    exact P.ker.sum_mem fun k _ => P.ker.mul_mem_left _ (hf k)
  · intro j
    have he : eval a (pderiv j (F i)) = (U * A) i j := by
      change eval a (pderiv j (F i)) = ∑ k, U i k * A k j
      simp only [F, map_sum, pderiv_C_mul, map_mul, eval_C, A]
    rw [he]
    exact hrow j

end Algebra.Generators
