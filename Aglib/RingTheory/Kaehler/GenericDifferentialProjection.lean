/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.FieldGenerators
public import Aglib.LinearAlgebra.Matrix.GenericProjection
public import Mathlib.LinearAlgebra.Basis.Defs

/-! # Actual nonzero projection polynomials from field generators

A displayed differential basis turns the differentials of the original field
generators into a spanning coordinate matrix. This produces a full-row minor
and a nonzero generic determinant, rather than assuming either one.
The change of ground field under generic parameter extension is separate.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace KaehlerDifferential

variable {k K ι : Type*} [Field k] [Field K] [Algebra k K] [Fintype ι] {d : ℕ}

/-- Actual field generation produces a nonzero full-row differential minor and
its nonzero generic projection determinant. -/
theorem exists_minor_and_genericProjection_det_ne_zero (x : ι → K)
    (hx : IntermediateField.adjoin k (Set.range x) = ⊤)
    (b : Module.Basis (Fin d) K (KaehlerDifferential k K)) :
    let A : Matrix (Fin d) ι K := fun i j => b.equivFun (D k K (x j)) i
    (∃ c : Fin d → ι, (A.submatrix id c).det ≠ 0) ∧
      (Matrix.genericProjection A).det ≠ 0 := by
  let A : Matrix (Fin d) ι K := fun i j => b.equivFun (D k K (x j)) i
  have hA : Submodule.span K (Set.range Aᵀ) = ⊤ := by
    change Submodule.span K (Set.range (b.equivFun ∘ fun j => D k K (x j))) = ⊤
    rw [Set.range_comp]
    change Submodule.span K (b.equivFun.toLinearMap ''
      Set.range (fun j => D k K (x j))) = ⊤
    rw [← Submodule.map_span, span_range_D_of_adjoin_eq_top x hx, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr b.equivFun.surjective
  exact ⟨Matrix.exists_fullRow_minor_ne_zero_of_span_eq_top A hA,
    Matrix.genericProjection_det_ne_zero A hA⟩

end KaehlerDifferential
