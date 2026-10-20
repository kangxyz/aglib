/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Finiteness of tensor products of finite additive groups


Source: `R5Lab.Aglib.LinearAlgebra.TensorProduct.Finite`.
Packet SHA-256:
`5fb621136c44c054edad6f4d024976572ad22db8d3de939e2dfd599b814a258a`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
open scoped TensorProduct
namespace TensorProduct
/-- A tensor product of finite actual additive groups is finite. -/
theorem finite_of_finite (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    [Finite M] [Finite N] : Finite (M ⊗[ℤ] N) := by
  classical
  let := Fintype.ofFinite M
  let := Fintype.ofFinite N
  exact Finite.of_surjective
    (fun s : Finset (M × N) => ∑ p ∈ s, p.1 ⊗ₜ[ℤ] p.2)
    (fun x => by obtain ⟨s, hs⟩ := TensorProduct.exists_finset x; exact ⟨s, hs.symm⟩)

end TensorProduct
