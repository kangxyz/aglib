/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.Algebra.Algebra.Hom

/-!
# A native coalgebra from whole tensor-comparison diagrams

The existing comparison, multiplication pullback and two evaluation maps
supply the actual comultiplication and counit on the original module.
Whole associativity, naturality and unit diagrams prove the native laws
before any concrete realization. No replacement coalgebra object is used.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u a b l

namespace LinearEquiv

/-- Transport associativity along the given forward identifications. -/
theorem comparison_assoc
    {R : Type u} [CommSemiring R]
    {A : Type a} [AddCommMonoid A] [Module R A]
    {B : Type b} [AddCommMonoid B] [Module R B]
    {C : Type l} [AddCommMonoid C] [Module R C]
    {D : Type*} [AddCommMonoid D] [Module R D]
    {E : A ⊗[R] A ≃ₗ[R] B} {E₁ : B ⊗[R] A ≃ₗ[R] C} {E₂ : A ⊗[R] B ≃ₗ[R] D}
    {L : A ⊗[R] A →ₗ[R] B} {L₁ : B ⊗[R] A →ₗ[R] C} {L₂ : A ⊗[R] B →ₗ[R] D}
    {a : D →ₗ[R] C}
    (hE : E.toLinearMap = L) (hE₁ : E₁.toLinearMap = L₁) (hE₂ : E₂.toLinearMap = L₂)
    (h : L₁ ∘ₗ L.rTensor A =
      a ∘ₗ L₂ ∘ₗ L.lTensor A ∘ₗ (TensorProduct.assoc R A A A).toLinearMap) :
    E₁.toLinearMap ∘ₗ E.toLinearMap.rTensor A =
      (a ∘ₗ E₂.toLinearMap) ∘ₗ E.toLinearMap.lTensor A ∘ₗ
        (TensorProduct.assoc R A A A).toLinearMap := by
  simp only [hE, hE₁, hE₂, LinearMap.comp_assoc]
  exact h

/-- A whole original product diagram proves coassociativity before any realization. -/
theorem coassoc_of_product_diagram
    {R : Type u} [CommSemiring R]
    {A : Type a} [AddCommMonoid A] [Module R A]
    {B : Type b} [AddCommMonoid B] [Module R B]
    {L : Type l} [AddCommMonoid L] [Module R L]
    (C : A ⊗[R] A ≃ₗ[R] B) (D : B ⊗[R] A ≃ₗ[R] L)
    (E : A ⊗[R] B →ₗ[R] L) (u : A →ₗ[R] B)
    (uL uR : B →ₗ[R] L)
    (hcoh : D.toLinearMap ∘ₗ C.toLinearMap.rTensor A =
      E ∘ₗ C.toLinearMap.lTensor A ∘ₗ (TensorProduct.assoc R A A A).toLinearMap)
    (hL : uL ∘ₗ C.toLinearMap = D.toLinearMap ∘ₗ u.rTensor A)
    (hR : uR ∘ₗ C.toLinearMap = E ∘ₗ u.lTensor A)
    (hu : uL ∘ₗ u = uR ∘ₗ u) :
    let delta := C.symm.toLinearMap ∘ₗ u
    (TensorProduct.assoc R A A A).toLinearMap ∘ₗ delta.rTensor A ∘ₗ delta =
      delta.lTensor A ∘ₗ delta := by
  let delta := C.symm.toLinearMap ∘ₗ u
  have hC : C.toLinearMap ∘ₗ delta = u := by
    apply LinearMap.ext
    intro x
    exact C.apply_symm_apply (u x)
  have hKL : Function.Injective (D.toLinearMap ∘ₗ C.toLinearMap.rTensor A) :=
    D.injective.comp (TensorProduct.congr C (LinearEquiv.refl R A)).injective
  have hKR : Function.Injective (E ∘ₗ C.toLinearMap.lTensor A) := by
    intro x y hxy
    apply (TensorProduct.assoc R A A A).symm.injective
    apply hKL
    have hx := LinearMap.congr_fun hcoh ((TensorProduct.assoc R A A A).symm x)
    have hy := LinearMap.congr_fun hcoh ((TensorProduct.assoc R A A A).symm y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply] at hx hy
    exact hx.trans (hxy.trans hy.symm)
  have hLeft : D.toLinearMap ∘ₗ C.toLinearMap.rTensor A ∘ₗ
      delta.rTensor A ∘ₗ delta = uL ∘ₗ u := by
    calc
      _ = D.toLinearMap ∘ₗ (C.toLinearMap ∘ₗ delta).rTensor A ∘ₗ delta := by
        rw [LinearMap.rTensor_comp (M := A) (f := delta) (g := C.toLinearMap)]
        simp only [LinearMap.comp_assoc]
      _ = D.toLinearMap ∘ₗ u.rTensor A ∘ₗ delta := by rw [hC]
      _ = uL ∘ₗ u := by
        have hNative := congrArg (fun f => f ∘ₗ delta) hL
        simp only [LinearMap.comp_assoc, hC] at hNative
        exact hNative.symm
  have hRight : E ∘ₗ C.toLinearMap.lTensor A ∘ₗ
      delta.lTensor A ∘ₗ delta = uR ∘ₗ u := by
    calc
      _ = E ∘ₗ (C.toLinearMap ∘ₗ delta).lTensor A ∘ₗ delta := by
        rw [LinearMap.lTensor_comp (M := A) (f := delta) (g := C.toLinearMap)]
        simp only [LinearMap.comp_assoc]
      _ = E ∘ₗ u.lTensor A ∘ₗ delta := by rw [hC]
      _ = uR ∘ₗ u := by
        have hNative := congrArg (fun f => f ∘ₗ delta) hR
        simp only [LinearMap.comp_assoc, hC] at hNative
        exact hNative.symm
  have hCoherence := congrArg (fun f => f ∘ₗ delta.rTensor A ∘ₗ delta) hcoh
  have hFinal := hCoherence.symm.trans (hLeft.trans (hu.trans hRight.symm))
  apply LinearMap.ext
  intro x
  apply hKR
  have hValue := LinearMap.congr_fun hFinal x
  simp only [LinearMap.comp_apply] at hValue ⊢
  exact hValue

/-- The original left evaluation diagram proves the literal native counit equation. -/
theorem left_counit_of_product_diagram
    {R : Type u} [CommSemiring R]
    {A : Type a} [AddCommMonoid A] [Module R A]
    {B : Type b} [AddCommMonoid B] [Module R B]
    (C : A ⊗[R] A ≃ₗ[R] B) (u : A →ₗ[R] B) (e : A →ₗ[R] R)
    (point : B →ₗ[R] A)
    (hpoint : point ∘ₗ C.toLinearMap =
      (TensorProduct.lid R A).toLinearMap ∘ₗ e.rTensor A)
    (hunit : point ∘ₗ u = LinearMap.id) :
    let delta := C.symm.toLinearMap ∘ₗ u
    e.rTensor A ∘ₗ delta = TensorProduct.mk R R A 1 := by
  let delta := C.symm.toLinearMap ∘ₗ u
  have hC : C.toLinearMap ∘ₗ delta = u := by
    apply LinearMap.ext
    intro x
    exact C.apply_symm_apply (u x)
  have hNative := congrArg (fun f => f ∘ₗ delta) hpoint
  simp only [LinearMap.comp_assoc, hC, hunit] at hNative
  apply LinearMap.ext
  intro x
  apply (TensorProduct.lid R A).injective
  have hValue := LinearMap.congr_fun hNative x
  simp only [delta, LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.mk_apply,
    TensorProduct.lid_tmul, one_smul] at hValue ⊢
  exact hValue.symm

/-- The original right evaluation diagram proves the other native counit equation. -/
theorem right_counit_of_product_diagram
    {R : Type u} [CommSemiring R]
    {A : Type a} [AddCommMonoid A] [Module R A]
    {B : Type b} [AddCommMonoid B] [Module R B]
    (C : A ⊗[R] A ≃ₗ[R] B) (u : A →ₗ[R] B) (e : A →ₗ[R] R)
    (point : B →ₗ[R] A)
    (hpoint : point ∘ₗ C.toLinearMap =
      (TensorProduct.rid R A).toLinearMap ∘ₗ e.lTensor A)
    (hunit : point ∘ₗ u = LinearMap.id) :
    let delta := C.symm.toLinearMap ∘ₗ u
    e.lTensor A ∘ₗ delta = (TensorProduct.mk R A R).flip 1 := by
  let delta := C.symm.toLinearMap ∘ₗ u
  have hC : C.toLinearMap ∘ₗ delta = u := by
    apply LinearMap.ext
    intro x
    exact C.apply_symm_apply (u x)
  have hNative := congrArg (fun f => f ∘ₗ delta) hpoint
  simp only [LinearMap.comp_assoc, hC, hunit] at hNative
  apply LinearMap.ext
  intro x
  apply (TensorProduct.rid R A).injective
  have hValue := LinearMap.congr_fun hNative x
  simp only [delta, LinearMap.comp_apply, LinearMap.id_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, TensorProduct.rid_tmul, one_smul] at hValue ⊢
  exact hValue.symm

end LinearEquiv

namespace LinearEquiv

section AlgebraComparison

variable {R : Type u} [CommSemiring R]
  {A : Type a} [Semiring A] [Algebra R A]
  {B : Type b} [Semiring B] [Algebra R B]
  {S : Type l} [Semiring S] [Algebra R S]
  (C : A ⊗[R] A ≃ₗ[R] B) (t : A ⊗[R] A ≃ₗ[R] S) (Φ : S →ₐ[R] B)
  (hF : Φ.toLinearMap ∘ₗ t.toLinearMap = C.toLinearMap)

include hF

private theorem algebraComparison_injective : Function.Injective Φ := by
  intro x y hxy
  apply t.symm.injective
  apply C.injective
  have hx := LinearMap.congr_fun hF (t.symm x)
  have hy := LinearMap.congr_fun hF (t.symm y)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] at hx hy
  exact hx.symm.trans (hxy.trans hy)

/-- The original algebra comparison cancels the one given linear inverse. -/
theorem apply_symm_of_algebra_comparison (z : B) : Φ (t (C.symm z)) = z := by
  have h := LinearMap.congr_fun hF (C.symm z)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, AlgHom.toLinearMap_apply] using h

/-- The actual inverse pullback preserves the original tensor unit. -/
theorem inverse_one_of_algebra_comparison (u : A →ₐ[R] B)
    (ht : t ((1 : A) ⊗ₜ[R] (1 : A)) = 1) :
    C.symm (u 1) = (1 : A) ⊗ₜ[R] (1 : A) := by
  apply t.injective
  apply algebraComparison_injective C t Φ hF
  simp only [apply_symm_of_algebra_comparison C t Φ hF, ht, map_one]

/-- The same inverse pullback is multiplicative in the selected target algebra. -/
theorem inverse_mul_of_algebra_comparison (u : A →ₐ[R] B) (a b : A) :
    t (C.symm (u (a * b))) = t (C.symm (u a)) * t (C.symm (u b)) := by
  apply algebraComparison_injective C t Φ hF
  simp only [map_mul, apply_symm_of_algebra_comparison C t Φ hF]

end AlgebraComparison

end LinearEquiv

namespace Coalgebra

variable {R : Type u} [CommSemiring R]
    {A : Type a} [AddCommMonoid A] [Module R A]
    {B : Type b} [AddCommMonoid B] [Module R B]
    {L : Type l} [AddCommMonoid L] [Module R L]
    (C : A ⊗[R] A ≃ₗ[R] B) (D : B ⊗[R] A ≃ₗ[R] L)
    (E : A ⊗[R] B →ₗ[R] L) (u : A →ₗ[R] B)
    (uL uR : B →ₗ[R] L) (e : A →ₗ[R] R) (pointL pointR : B →ₗ[R] A)
    (hcoh : D.toLinearMap ∘ₗ C.toLinearMap.rTensor A =
      E ∘ₗ C.toLinearMap.lTensor A ∘ₗ (TensorProduct.assoc R A A A).toLinearMap)
    (hL : uL ∘ₗ C.toLinearMap = D.toLinearMap ∘ₗ u.rTensor A)
    (hR : uR ∘ₗ C.toLinearMap = E ∘ₗ u.lTensor A)
    (hu : uL ∘ₗ u = uR ∘ₗ u)
    (hpointL : pointL ∘ₗ C.toLinearMap =
      (TensorProduct.lid R A).toLinearMap ∘ₗ e.rTensor A)
    (hpointR : pointR ∘ₗ C.toLinearMap =
      (TensorProduct.rid R A).toLinearMap ∘ₗ e.lTensor A)
    (hunitL : pointL ∘ₗ u = LinearMap.id)
    (hunitR : pointR ∘ₗ u = LinearMap.id)

/-- The native coalgebra on the SAME module, with comul the original comparison inverse
followed by the original multiplication pullback and counit the given original evaluation. -/
@[instance_reducible]
def ofTensorComparison : Coalgebra R A where
  comul := C.symm.toLinearMap ∘ₗ u
  counit := e
  coassoc := LinearEquiv.coassoc_of_product_diagram C D E u uL uR hcoh hL hR hu
  rTensor_counit_comp_comul :=
    LinearEquiv.left_counit_of_product_diagram C u e pointL hpointL hunitL
  lTensor_counit_comp_comul :=
    LinearEquiv.right_counit_of_product_diagram C u e pointR hpointR hunitR

/-- The complete comultiplication is the actual original inverse/composition operator. -/
theorem ofTensorComparison_comul :
    (ofTensorComparison C D E u uL uR e pointL pointR
      hcoh hL hR hu hpointL hpointR hunitL hunitR).comul = C.symm.toLinearMap ∘ₗ u := rfl

/-- The complete counit is exactly the original evaluation map. -/
theorem ofTensorComparison_counit :
    (ofTensorComparison C D E u uL uR e pointL pointR
      hcoh hL hR hu hpointL hpointR hunitL hunitR).counit = e := rfl

end Coalgebra

namespace Coalgebra

/-- Assemble the original coalgebra with its comparisons inferred from associativity. -/
@[instance_reducible]
def ofTensorComparisonFromAssoc
    {R : Type u} [CommSemiring R]
    {A : Type a} [AddCommMonoid A] [Module R A]
    {B : Type b} [AddCommMonoid B] [Module R B]
    {L : Type l} [AddCommMonoid L] [Module R L]
    {C : A ⊗[R] A ≃ₗ[R] B} {D : B ⊗[R] A ≃ₗ[R] L} {E : A ⊗[R] B →ₗ[R] L}
    (hcoh : D.toLinearMap ∘ₗ C.toLinearMap.rTensor A =
      E ∘ₗ C.toLinearMap.lTensor A ∘ₗ (TensorProduct.assoc R A A A).toLinearMap)
    (u : A →ₗ[R] B) (uL uR : B →ₗ[R] L)
    (e : A →ₗ[R] R) (pointL pointR : B →ₗ[R] A)
    (hL : uL ∘ₗ C.toLinearMap = D.toLinearMap ∘ₗ u.rTensor A)
    (hR : uR ∘ₗ C.toLinearMap = E ∘ₗ u.lTensor A)
    (hu : uL ∘ₗ u = uR ∘ₗ u)
    (hpointL : pointL ∘ₗ C.toLinearMap =
      (TensorProduct.lid R A).toLinearMap ∘ₗ e.rTensor A)
    (hpointR : pointR ∘ₗ C.toLinearMap =
      (TensorProduct.rid R A).toLinearMap ∘ₗ e.lTensor A)
    (hunitL : pointL ∘ₗ u = LinearMap.id) (hunitR : pointR ∘ₗ u = LinearMap.id) :
    Coalgebra R A :=
  ofTensorComparison C D E u uL uR e pointL pointR hcoh hL hR hu hpointL hpointR hunitL hunitR

end Coalgebra
