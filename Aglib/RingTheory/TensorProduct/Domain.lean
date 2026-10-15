/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Adjoin.FGBaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor products of domains over an algebraically closed field

The tensor product of two domain algebras over an algebraically closed field is
a domain. Finite-type subalgebras supply rational coefficient specializations
inside the proof; no finite-type condition is imposed on either final algebra.

## Extraction basis

Transferred from `R5Lab.RingTheory.TensorProduct.Domain` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`66ee85396cc4b6eb3599a632079ab82b5e6dc19305dd091401bd6df5882cefdc`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped _root_.TensorProduct

namespace Algebra.TensorProduct

universe u v w

/-- A nonzero element of a finite-type domain over an algebraically closed
field remains nonzero at some rational specialization. -/
theorem _root_.Algebra.FiniteType.exists_specialization_ne_zero
    (k : Type u) [Field k] [IsAlgClosed k]
    (B : Type v) [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (b : B) (hb : b ≠ 0) :
    ∃ φ : B →ₐ[k] k, φ b ≠ 0 := by
  let : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hn : b ∉ (⊥ : Ideal B).jacobson := by
    rw [isJacobsonRing_iff_prime_eq.mp inferInstance ⊥ inferInstance, Ideal.mem_bot]
    exact hb
  have hm : ∃ m : Ideal B, m.IsMaximal ∧ b ∉ m := by
    by_contra! h
    apply hn
    rw [Ideal.jacobson, Ideal.mem_sInf]
    intro m hm
    exact h m hm.2
  obtain ⟨m, hm, hbm⟩ := hm
  let := hm
  let := Ideal.Quotient.field m
  let := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
  let e : (B ⧸ m) ≃ₐ[k] k :=
    (AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ m))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm
  refine ⟨e.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  intro hz
  apply hbm
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply e.injective
  simpa using hz

/-- Rational specialization of the right tensor factor, as an actual algebra
homomorphism into the left domain. -/
def specializeTensor
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    {B : Type w} [CommRing B] [Algebra k B] (φ : B →ₐ[k] k) :
    A ⊗[k] B →ₐ[k] A :=
  (Algebra.TensorProduct.rid k k A).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k A) φ)

/-- Specialization commutes with every coefficient relative to a basis of the
left factor. -/
theorem specializeTensor_coordinate
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    {B : Type w} [CommRing B] [Algebra k B]
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k A) (φ : B →ₐ[k] k)
    (z : A ⊗[k] B) (i : ι) :
    b.repr (specializeTensor φ z) i =
      φ (_root_.TensorProduct.equivFinsuppOfBasisLeft b z i) := by
  classical
  induction z using _root_.TensorProduct.inductionOn with
  | tmul a d =>
    simp [specializeTensor, Algebra.TensorProduct.rid_tmul,
      mul_comm]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- Tensoring any domain with a finite-type domain over an algebraically closed
field does not introduce zero divisors. -/
theorem tensorProduct_noZeroDivisors_finiteType
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra k A]
    (B : Type w) [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] : NoZeroDivisors (A ⊗[k] B) := by
  classical
  let b := Module.Free.chooseBasis k A
  let c := _root_.TensorProduct.equivFinsuppOfBasisLeft (N := B) b
  constructor
  intro x y hxy
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hy : y = 0
  · exact Or.inr hy
  have hxc : ∃ i, c x i ≠ 0 := by
    by_contra! h
    apply hx
    apply c.injective
    ext i
    simpa using h i
  have hyc : ∃ j, c y j ≠ 0 := by
    by_contra! h
    apply hy
    apply c.injective
    ext j
    simpa using h j
  obtain ⟨i, hi⟩ := hxc
  obtain ⟨j, hj⟩ := hyc
  obtain ⟨φ, hφ⟩ :=
    Algebra.FiniteType.exists_specialization_ne_zero k B (c x i * c y j) (mul_ne_zero hi hj)
  have hφx : specializeTensor φ x ≠ 0 := by
    intro hz
    apply hφ
    rw [map_mul]
    have h := specializeTensor_coordinate b φ x i
    rw [hz, map_zero, Finsupp.zero_apply] at h
    change 0 = φ (c x i) at h
    rw [← h, zero_mul]
  have hφy : specializeTensor φ y ≠ 0 := by
    intro hz
    apply hφ
    rw [map_mul]
    have h := specializeTensor_coordinate b φ y j
    rw [hz, map_zero, Finsupp.zero_apply] at h
    change 0 = φ (c y j) at h
    rw [← h, mul_zero]
  exact False.elim ((mul_ne_zero hφx hφy) (by
    rw [← map_mul, hxy, map_zero]))

/-- Tensoring arbitrary domains over an algebraically closed field introduces
no zero divisors. The finite-type specialization is applied only to a single
finitely generated subalgebra containing the two finite tensor expressions. -/
theorem tensorProduct_noZeroDivisors
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra k A]
    (B : Type w) [CommRing B] [IsDomain B] [Algebra k B] :
    NoZeroDivisors (A ⊗[k] B) := by
  constructor
  intro x y hxy
  obtain ⟨B₁, hB₁, x', hx⟩ := exists_fg_and_mem_baseChange x
  obtain ⟨B₂, hB₂, y', hy⟩ := exists_fg_and_mem_baseChange y
  let D := B₁ ⊔ B₂
  let : Algebra.FiniteType k D := ⟨D.fg_top.mpr (hB₁.sup hB₂)⟩
  let : NoZeroDivisors (A ⊗[k] D) := tensorProduct_noZeroDivisors_finiteType k A D
  let i₁ : B₁ →ₐ[k] D := Subalgebra.inclusion le_sup_left
  let i₂ : B₂ →ₐ[k] D := Subalgebra.inclusion le_sup_right
  let f₁ : A ⊗[k] B₁ →ₐ[A] A ⊗[k] D :=
    Algebra.TensorProduct.map (AlgHom.id A A) i₁
  let f₂ : A ⊗[k] B₂ →ₐ[A] A ⊗[k] D :=
    Algebra.TensorProduct.map (AlgHom.id A A) i₂
  let f : A ⊗[k] D →ₐ[A] A ⊗[k] B :=
    Algebra.TensorProduct.map (AlgHom.id A A) D.val
  have hf : Function.Injective f := by
    change Function.Injective (D.val.toLinearMap.lTensor A)
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hf₁ : f.comp f₁ = Algebra.TensorProduct.map (AlgHom.id A A) B₁.val := by
    ext a
    rfl
  have hf₂ : f.comp f₂ = Algebra.TensorProduct.map (AlgHom.id A A) B₂.val := by
    ext a
    rfl
  have hx' : f (f₁ x') = x := by
    rw [← AlgHom.comp_apply, hf₁]
    exact hx
  have hy' : f (f₂ y') = y := by
    rw [← AlgHom.comp_apply, hf₂]
    exact hy
  have hz : f₁ x' * f₂ y' = 0 := hf (by
    rw [map_mul, hx', hy', hxy, map_zero])
  rcases mul_eq_zero.mp hz with hx0 | hy0
  · exact Or.inl (hx'.symm.trans (by rw [hx0, map_zero]))
  · exact Or.inr (hy'.symm.trans (by rw [hy0, map_zero]))

/-- The tensor product of any two domains over an algebraically closed field
is a nontrivial domain, including arbitrary extension fields. -/
theorem tensorProduct_isDomain
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra k A]
    (B : Type w) [CommRing B] [IsDomain B] [Algebra k B] :
    IsDomain (A ⊗[k] B) := by
  let : NoZeroDivisors (A ⊗[k] B) := tensorProduct_noZeroDivisors k A B
  let : Nontrivial (A ⊗[k] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k A B
      (RingHom.injective (algebraMap k B))
  exact NoZeroDivisors.to_isDomain _

end Algebra.TensorProduct
