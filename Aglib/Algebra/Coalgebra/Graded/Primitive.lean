/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Coalgebra.Graded.Dimension

/-!
# Primitivity from the degree-one coproduct grading

In degree one the native tensor projections leave just bidegrees `(0,1)`
and `(1,0)`. Connectedness identifies the degree-zero projection with
the original counit followed by scalar inclusion. The two native counit
identities then identify both surviving components and prove primitivity.

The endpoint combines this grading calculation with the dimension bound.
All hypotheses concern the original grading and coalgebra maps; no
primitive-element assertion is passed to that endpoint.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace GradedAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [Coalgebra R A]
  (hε : ∀ a, GradedAlgebra.proj 𝒜 0 a = Coalgebra.counit (R := R) a • (1 : A))

include hε

/-- The `(0,*)` projection of the original coproduct is its left counit
identity, with the degree-zero scalar included back into the algebra. -/
theorem map_proj_zero_id_comul (a : A) :
    TensorProduct.map (GradedAlgebra.proj 𝒜 0) LinearMap.id
      (Coalgebra.comul (R := R) a) = (1 : A) ⊗ₜ[R] a := by
  let s : R →ₗ[R] A := LinearMap.toSpanSingleton R A 1
  have hp : s ∘ₗ Coalgebra.counit = GradedAlgebra.proj 𝒜 0 := by
    ext b
    exact (hε b).symm
  have h := congrArg (TensorProduct.map s (LinearMap.id : A →ₗ[R] A))
    (Coalgebra.rTensor_counit_comul (R := R) a)
  simpa [LinearMap.rTensor, TensorProduct.map_map, hp, s] using h

/-- The `(*,0)` projection of the original coproduct is its right counit
identity with scalar inclusion. -/
theorem map_id_proj_zero_comul (a : A) :
    TensorProduct.map LinearMap.id (GradedAlgebra.proj 𝒜 0)
      (Coalgebra.comul (R := R) a) = a ⊗ₜ[R] (1 : A) := by
  let s : R →ₗ[R] A := LinearMap.toSpanSingleton R A 1
  have hp : s ∘ₗ Coalgebra.counit = GradedAlgebra.proj 𝒜 0 := by
    ext b
    exact (hε b).symm
  have h := congrArg (TensorProduct.map (LinearMap.id : A →ₗ[R] A) s)
    (Coalgebra.lTensor_counit_comul (R := R) a)
  simpa [LinearMap.lTensor, TensorProduct.map_map, hp, s] using h

end GradedAlgebra

namespace GradedAlgebra

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] [Nontrivial A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] [Coalgebra k A]

/-- A degree-one element is primitive as soon as the coproduct has only
the two bidegrees permitted by its grading. -/
theorem isSkewPrimitiveElem_of_comul_degreeOne
    (hε : ∀ a, GradedAlgebra.proj 𝒜 0 a = Coalgebra.counit (R := k) a • (1 : A))
    (x : 𝒜 1)
    (hdegree :
      TensorProduct.map (GradedAlgebra.proj 𝒜 0) (GradedAlgebra.proj 𝒜 1)
          (Coalgebra.comul (x : A)) +
        TensorProduct.map (GradedAlgebra.proj 𝒜 1) (GradedAlgebra.proj 𝒜 0)
          (Coalgebra.comul (x : A)) = Coalgebra.comul (x : A)) :
    Coalgebra.IsSkewPrimitiveElem k (1 : A) 1 (x : A) where
  counit_eq_zero := by
    have hz : Coalgebra.counit (R := k) (x : A) • (1 : A) = 0 := by
      rw [← hε, GradedAlgebra.proj_apply]
      exact DirectSum.decompose_of_mem_ne 𝒜 x.property (by decide)
    exact (smul_eq_zero.mp hz).resolve_right one_ne_zero
  comul_eq_tmul_add_tmul := by
    have hx : GradedAlgebra.proj 𝒜 1 (x : A) = x :=
      DirectSum.decompose_of_mem_same 𝒜 x.property
    have hleft := congrArg
      (TensorProduct.map (LinearMap.id : A →ₗ[k] A) (GradedAlgebra.proj 𝒜 1))
      (map_proj_zero_id_comul 𝒜 hε (x : A))
    have hright := congrArg
      (TensorProduct.map (GradedAlgebra.proj 𝒜 1) (LinearMap.id : A →ₗ[k] A))
      (map_id_proj_zero_comul 𝒜 hε (x : A))
    simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id,
      TensorProduct.map_tmul, LinearMap.id_apply, hx] at hleft hright
    rw [← hdegree, hleft, hright]

/-- The degree-one dimension bound from the actual connected grading,
native counit laws, and signed multiplication law of the coproduct.
Only the degree-one part of coproduct grading is needed. -/
theorem finrank_degreeOne_le_of_comul_grading [Module.Finite k (𝒜 1)]
    (hε : ∀ a, GradedAlgebra.proj 𝒜 0 a = Coalgebra.counit (R := k) a • (1 : A))
    (h_one : Coalgebra.comul (R := k) (1 : A) = (1 : A) ⊗ₜ[k] (1 : A))
    (h_mul : ∀ a b : A,
      GradedTensorProduct.of k 𝒜 𝒜 (Coalgebra.comul (a * b)) =
        GradedTensorProduct.of k 𝒜 𝒜 (Coalgebra.comul a) *
          GradedTensorProduct.of k 𝒜 𝒜 (Coalgebra.comul b))
    (hdegree : ∀ x : 𝒜 1,
      TensorProduct.map (GradedAlgebra.proj 𝒜 0) (GradedAlgebra.proj 𝒜 1)
          (Coalgebra.comul (x : A)) +
        TensorProduct.map (GradedAlgebra.proj 𝒜 1) (GradedAlgebra.proj 𝒜 0)
          (Coalgebra.comul (x : A)) = Coalgebra.comul (x : A))
    (g : ℕ) (hvanish : ∀ n, g < n → 𝒜 n = ⊥) :
    Module.finrank k (𝒜 1) ≤ g :=
  finrank_degreeOne_le_of_vanishing 𝒜 hε h_one h_mul
    (fun x => isSkewPrimitiveElem_of_comul_degreeOne 𝒜 hε x (hdegree x)) g hvanish

end GradedAlgebra
