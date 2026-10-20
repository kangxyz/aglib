/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.ScalarHomology.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic

/-!
# Principal tensor specialization and actual cokernel lengths

Source-only extraction from `R5Lab.KTheory.Module.CommutingAutomorphisms.PrincipalFaceCokernel` at
R5Lab revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing objects, maps,
hypotheses, universes, proof bodies and mathematical namespaces are retained.
The original source correspondence remains in the supplying application module.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Length/TensorSpecialization.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`0b19bed74976d720e09e4b7ba04360a476cd7eb98d1ee9fbc976a6c4ebdf5777`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module
universe u v w
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (N : Type w) [AddCommGroup N] [Module A N]

/-- The actual tensor specialization map.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded generic subset: the canonical A-linear map N -> B tensor_A N for arbitrary
commutative A-algebras and A-modules. -/
def tensorSpecialization : N →ₗ[A] B ⊗[A] N := TensorProduct.mk A B N 1
/-- A surjective structural algebra map makes the canonical tensor specialization
surjective.

Supporting helper for the module's explicit original principal-face/local-coefficient
source mapping. -/
theorem tensorSpecialization_surjective (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (tensorSpecialization (A := A) (B := B) N) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b n =>
    obtain ⟨a, rfl⟩ := h b
    refine ⟨a • n, ?_⟩
    change (1 : B) ⊗ₜ[A] (a • n) = (algebraMap A B a) ⊗ₜ[A] n
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

/-- Surjective principal specialization has kernel equal to the range of multiplication by
t, without requiring flatness of N.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded generic subset: surjective A -> B with kernel (t) gives the specialization
kernel range(t); N need not be flat. -/
theorem ker_tensorSpecialization (t : A)
    (h : Function.Surjective (algebraMap A B))
    (ht : RingHom.ker (algebraMap A B) = Ideal.span ({t} : Set A)) :
    LinearMap.ker (tensorSpecialization (A := A) (B := B) N) =
      LinearMap.range (LinearMap.lsmul A N t) := by
  let f : A →ₗ[A] A := LinearMap.lsmul A A t
  let g : A →ₗ[A] B := Algebra.linearMap A B
  have hex : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    ext a
    change algebraMap A B a = 0 ↔ (∃ b, t • b = a)
    rw [← RingHom.mem_ker, ht, Ideal.mem_span_singleton]
    simp only [smul_eq_mul, dvd_def, eq_comm]
  have htex := rTensor_exact N hex h
  have hunit : (g.rTensor N).comp (TensorProduct.lid A N).symm.toLinearMap =
      tensorSpecialization (A := A) (B := B) N := by
    ext n
    simp [g, tensorSpecialization]
  have hmul : (TensorProduct.lid A N).toLinearMap.comp (f.rTensor N) =
      (LinearMap.lsmul A N t).comp (TensorProduct.lid A N).toLinearMap := by
    ext
    simp [f]
  ext n
  constructor
  · intro hn
    have hk : (TensorProduct.lid A N).symm n ∈ LinearMap.ker (g.rTensor N) := by
      change (g.rTensor N) ((TensorProduct.lid A N).symm n) = 0
      exact (LinearMap.congr_fun hunit n).trans hn
    rw [htex.linearMap_ker_eq] at hk
    obtain ⟨z, hz⟩ := hk
    refine ⟨(TensorProduct.lid A N).toLinearMap z, ?_⟩
    have hh := congrArg (TensorProduct.lid A N) hz
    have hm := LinearMap.congr_fun hmul z
    simpa only [LinearMap.comp_apply, LinearEquiv.apply_symm_apply] using hm.symm.trans hh
  · rintro ⟨z, rfl⟩
    change tensorSpecialization (A := A) (B := B) N (t • z) = 0
    have hz : algebraMap A B t = 0 :=
      RingHom.mem_ker.mp (ht.symm ▸ Ideal.subset_span (Set.mem_singleton t))
    change (1 : B) ⊗ₜ[A] (t • z) = 0
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, hz, zero_mul,
      TensorProduct.zero_tmul]
/-- The canonical principal quotient is the actual tensor specialization target, without a
flatness assumption on N.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded generic subset: the canonical quotient equivalence for surjective A -> B with
kernel (t), without flatness of N. -/
def tensorSpecializationCokernelEquiv (t : A)
    (h : Function.Surjective (algebraMap A B))
    (ht : RingHom.ker (algebraMap A B) = Ideal.span ({t} : Set A)) :
    (N ⧸ LinearMap.range (LinearMap.lsmul A N t)) ≃ₗ[A] B ⊗[A] N :=
  (Submodule.quotEquivOfEq _ _ (ker_tensorSpecialization N t h ht).symm).trans
    ((tensorSpecialization (A := A) (B := B) N).quotKerEquivOfSurjective
      (tensorSpecialization_surjective N h))

/-- Equal endomorphisms have equal literal cokernel lengths.

Supporting helper for the module's explicit original principal-face/local-coefficient
source mapping. -/
theorem endCokernel_length_congr (f g : N →ₗ[A] N) (h : f = g) :
    Module.length A (N ⧸ LinearMap.range f) =
      Module.length A (N ⧸ LinearMap.range g) := by
  cases h
  rfl

end Module
