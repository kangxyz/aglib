/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Adjoin.FG

/-!
# Finite coefficient data in algebra tensor products

A finite family of tensors and prescribed scalar coefficients lift through a
finitely generated coefficient subalgebra, with the actual tensor map.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Smooth/FiniteModel.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`224517fcfb1a8866ec9f4f41dc6e6e131874f84ede9b359b0f631e61df6db3fd`.
-/

@[expose] public section

noncomputable section
open _root_.TensorProduct
namespace Algebra.TensorProduct
universe u v w
section FiniteTensorData

variable {R : Type u} [CommRing R] {C : Type v} [CommRing C] [Algebra R C]
  {D : Type w} [CommRing D] [Algebra R D]

/-- A finite family of tensors uses finitely many coefficients in its first factor. -/
theorem exists_fg_tensor_lifts (data : Finset (C ⊗[R] D)) (extra : Finset C) :
    ∃ S : Subalgebra R C, S.FG ∧ (∀ c ∈ extra, c ∈ S) ∧
      ∀ z ∈ data, ∃ y : S ⊗[R] D, Algebra.TensorProduct.rTensor D S.val y = z := by
  classical
  choose T hT using fun z : data => _root_.TensorProduct.exists_finset (z : C ⊗[R] D)
  let coeffs : Finset C := extra ∪ Finset.univ.biUnion
    (fun z : data => (T z).image Prod.fst)
  let S : Subalgebra R C := Algebra.adjoin R (coeffs : Set C)
  refine ⟨S, ⟨coeffs, rfl⟩, ?_, ?_⟩
  · intro c hc
    exact Algebra.subset_adjoin (Finset.mem_union_left _ hc)
  · intro z hz
    let z' : data := ⟨z, hz⟩
    have hcoeff (p : C × D) (hp : p ∈ T z') : p.1 ∈ S := by
      apply Algebra.subset_adjoin
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨z', Finset.mem_univ _, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩)
    change (z' : C ⊗[R] D) ∈ (Algebra.TensorProduct.rTensor D S.val).range
    rw [hT z']
    apply Subalgebra.sum_mem
    intro p hp
    refine ⟨(⟨p.1, hcoeff p hp⟩ : S) ⊗ₜ[R] p.2, ?_⟩
    simp

end FiniteTensorData
end Algebra.TensorProduct
