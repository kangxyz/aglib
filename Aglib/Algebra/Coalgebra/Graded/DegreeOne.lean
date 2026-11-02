/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Coalgebra.Primitive

/-!
# Contraction in degree one of a graded coalgebra

The tensor product is Mathlib's Koszul-signed `GradedTensorProduct`. The
coproduct and counit remain the original native `Coalgebra` maps. Contracting
the first factor against a degree-one functional removes a primitive
degree-one factor by the signed Leibniz formula.

No ordinary, unsigned `Bialgebra` structure is asserted. Neither
cocommutativity, an antipode, nor graded commutativity is used.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace GradedAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- A degree-one functional, extended by zero in every other degree. -/
def degreeOneFunctional (f : Module.Dual R (𝒜 1)) : Module.Dual R A :=
  f ∘ₗ (DFinsupp.lapply 1) ∘ₗ (DirectSum.decomposeAlgEquiv 𝒜).toLinearMap

@[simp]
theorem degreeOneFunctional_coe (f : Module.Dual R (𝒜 1)) (x : 𝒜 1) :
    degreeOneFunctional 𝒜 f (x : A) = f x := by
  change f (DirectSum.decompose 𝒜 (x : A) 1) = f x
  simp

theorem degreeOneFunctional_of_mem_ne (f : Module.Dual R (𝒜 1))
    {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) (hn : n ≠ 1) :
    degreeOneFunctional 𝒜 f a = 0 := by
  have h : DirectSum.decompose 𝒜 a 1 = 0 :=
    Subtype.ext (DirectSum.decompose_of_mem_ne 𝒜 ha hn)
  change f (DirectSum.decompose 𝒜 a 1) = 0
  rw [h, map_zero]

@[simp]
theorem degreeOneFunctional_one (f : Module.Dual R (𝒜 1)) :
    degreeOneFunctional 𝒜 f (1 : A) = 0 :=
  degreeOneFunctional_of_mem_ne 𝒜 f (SetLike.one_mem_graded 𝒜) (by decide)

/-- In a connected augmented grading, multiplication by a degree-one
element only sees the degree-zero part of the other factor. -/
theorem degreeOneFunctional_mul (ε : A →ₗ[R] R)
    (hε : ∀ a, GradedAlgebra.proj 𝒜 0 a = ε a • (1 : A))
    (f : Module.Dual R (𝒜 1)) (x : 𝒜 1) (a : A) :
    degreeOneFunctional 𝒜 f ((x : A) * a) = f x * ε a := by
  have h : DirectSum.decompose 𝒜 ((x : A) * a) 1 = ε a • x := by
    apply Subtype.ext
    change (DirectSum.decompose 𝒜 ((x : A) * a) 1 : A) = ε a • (x : A)
    calc
      _ = (x : A) * GradedAlgebra.proj 𝒜 0 a := by
        simpa only [Nat.add_zero, GradedAlgebra.proj_apply] using
          (DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (j := 0) x.property (b := a))
      _ = _ := by rw [hε, mul_smul_comm, mul_one]
  change f (DirectSum.decompose 𝒜 ((x : A) * a) 1) = _
  rw [h, map_smul, smul_eq_mul, mul_comm]

/-- Contraction of the first factor of the native signed tensor product. -/
def tensorContraction (f : Module.Dual R A) : (𝒜 ᵍ⊗[R] 𝒜) →ₗ[R] A :=
  TensorProduct.lift ((LinearMap.lsmul R A) ∘ₗ f) ∘ₗ
    (GradedTensorProduct.of R 𝒜 𝒜).symm.toLinearMap

@[simp]
theorem tensorContraction_tmul (f : Module.Dual R A) (a b : A) :
    tensorContraction 𝒜 f (a ᵍ⊗ₜ[R] b) = f a • b := rfl

/-- The signed tensor calculation behind contraction of a primitive
degree-one factor. It is valid over every commutative base ring. -/
theorem tensorContraction_primitive_mul (ε : A →ₗ[R] R)
    (hε : ∀ a, GradedAlgebra.proj 𝒜 0 a = ε a • (1 : A))
    (f : Module.Dual R (𝒜 1)) (x : 𝒜 1) (t : 𝒜 ᵍ⊗[R] 𝒜) :
    tensorContraction 𝒜 (degreeOneFunctional 𝒜 f)
        (((x : A) ᵍ⊗ₜ[R] (1 : A) + (1 : A) ᵍ⊗ₜ[R] (x : A)) * t) =
      f x • tensorContraction 𝒜 ε t -
        (x : A) * tensorContraction 𝒜 (degreeOneFunctional 𝒜 f) t := by
  suffices h :
      (tensorContraction 𝒜 (degreeOneFunctional 𝒜 f)).comp
          (LinearMap.mulLeft R
            ((x : A) ᵍ⊗ₜ[R] (1 : A) + (1 : A) ᵍ⊗ₜ[R] (x : A))) =
        f x • tensorContraction 𝒜 ε -
          (LinearMap.mulLeft R (x : A)).comp
            (tensorContraction 𝒜 (degreeOneFunctional 𝒜 f)) from
    LinearMap.congr_fun h t
  apply GradedTensorProduct.hom_ext
  ext a b
  change tensorContraction 𝒜 (degreeOneFunctional 𝒜 f)
      (((x : A) ᵍ⊗ₜ[R] (1 : A) + (1 : A) ᵍ⊗ₜ[R] (x : A)) *
        (a ᵍ⊗ₜ[R] b)) =
    f x • tensorContraction 𝒜 ε (a ᵍ⊗ₜ[R] b) -
      (x : A) * tensorContraction 𝒜 (degreeOneFunctional 𝒜 f) (a ᵍ⊗ₜ[R] b)
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp [GradedTensorProduct.tmul]
  | add a a' ha ha' =>
      simp only [GradedTensorProduct.tmul, TensorProduct.add_tmul, map_add,
        mul_add, smul_add, ha, ha']
      abel
  | @homogeneous n a =>
      rw [add_mul, map_add, GradedTensorProduct.tmul_one_mul_coe_tmul,
        GradedTensorProduct.tmul_coe_mul_coe_tmul]
      simp only [one_mul, tensorContraction_tmul,
        degreeOneFunctional_mul 𝒜 ε hε, mul_smul]
      by_cases hn : n = 1
      · subst n
        simp [Units.smul_def, sub_eq_add_neg]
      · have hf : degreeOneFunctional 𝒜 f (a : A) = 0 :=
          degreeOneFunctional_of_mem_ne 𝒜 f a.property hn
        rw [LinearMap.map_smul_of_tower, tensorContraction_tmul, hf]
        simp

section Coalgebra

variable [Coalgebra R A]

/-- A signed algebra coproduct constructed from the original native
coalgebra map and its multiplication and unit laws. -/
def comulAlgHom
    (h_one : Coalgebra.comul (R := R) (1 : A) = (1 : A) ⊗ₜ[R] (1 : A))
    (h_mul : ∀ a b : A,
      GradedTensorProduct.of R 𝒜 𝒜 (Coalgebra.comul (a * b)) =
        GradedTensorProduct.of R 𝒜 𝒜 (Coalgebra.comul a) *
          GradedTensorProduct.of R 𝒜 𝒜 (Coalgebra.comul b)) :
    A →ₐ[R] (𝒜 ᵍ⊗[R] 𝒜) :=
  AlgHom.ofLinearMap
    ((GradedTensorProduct.of R 𝒜 𝒜).toLinearMap ∘ₗ Coalgebra.comul)
    (by change GradedTensorProduct.of R 𝒜 𝒜 (Coalgebra.comul 1) = 1; rw [h_one]; rfl)
    h_mul

/-- Degree-one contraction of the original comultiplication. -/
def contraction (f : Module.Dual R (𝒜 1)) : A →ₗ[R] A :=
  TensorProduct.lift ((LinearMap.lsmul R A) ∘ₗ degreeOneFunctional 𝒜 f) ∘ₗ
    Coalgebra.comul

@[simp]
theorem contraction_one
    (h_one : Coalgebra.comul (R := R) (1 : A) = (1 : A) ⊗ₜ[R] (1 : A))
    (f : Module.Dual R (𝒜 1)) : contraction 𝒜 f 1 = 0 := by
  simp [contraction, h_one]

/-- Contraction removes a primitive degree-one factor by the signed
Leibniz formula. No invertibility assumption on 2 occurs. -/
theorem contraction_primitive_mul
    (hε : ∀ a, GradedAlgebra.proj 𝒜 0 a = Coalgebra.counit (R := R) a • (1 : A))
    (h_mul : ∀ a b : A,
      GradedTensorProduct.of R 𝒜 𝒜 (Coalgebra.comul (a * b)) =
        GradedTensorProduct.of R 𝒜 𝒜 (Coalgebra.comul a) *
          GradedTensorProduct.of R 𝒜 𝒜 (Coalgebra.comul b))
    (f : Module.Dual R (𝒜 1)) (x : 𝒜 1)
    (hx : Coalgebra.IsSkewPrimitiveElem R (1 : A) 1 (x : A)) (a : A) :
    contraction 𝒜 f ((x : A) * a) = f x • a - (x : A) * contraction 𝒜 f a := by
  change tensorContraction 𝒜 (degreeOneFunctional 𝒜 f)
      (GradedTensorProduct.of R 𝒜 𝒜 (Coalgebra.comul ((x : A) * a))) = _
  rw [h_mul, hx.comul_eq_tmul_add_tmul, map_add, add_comm]
  rw [tensorContraction_primitive_mul 𝒜 _ hε]
  congr 2
  exact LinearMap.congr_fun Coalgebra.lift_lsmul_comp_counit_comp_comul a

end Coalgebra

end GradedAlgebra
