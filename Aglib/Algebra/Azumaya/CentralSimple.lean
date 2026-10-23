/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Module.Bimodule
public import Mathlib.LinearAlgebra.Basis.MulOpposite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.SimpleRing.Congr

/-!
# Finite-dimensional central simple algebras are Azumaya

The action is the native tensor bimodule action. Simplicity is proved by
turning its submodules into two-sided ideals. Its commuting endomorphisms are
scalars by centrality, so native Jacobson density proves surjectivity of the
original `AlgHom.mulLeftRight`; equal dimensions then give injectivity.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open MulOpposite

attribute [local instance] TensorProduct.Algebra.module

namespace IsSimpleRing

variable (K A : Type*) [Field K] [Ring A] [Algebra K A] [IsSimpleRing A]

/-- A simple algebra is a simple module for its native left-right tensor action. -/
theorem isSimpleModule_tensor_mulOpposite : IsSimpleModule (A ⊗[K] Aᵐᵒᵖ) A where
  eq_bot_or_eq_top P := by
    let I : Ideal A := Subbimodule.toSubmodule P
    have hI : I.IsTwoSided := ⟨fun b ha => by
      exact Subbimodule.smul_mem' P (op b) ha⟩
    obtain h | h := (isSimpleRing_iff_isTwoSided_imp.mp ‹IsSimpleRing A›).2 I hI
    · left
      ext x
      change x ∈ I ↔ x ∈ (⊥ : Ideal A)
      rw [h]
    · right
      ext x
      change x ∈ I ↔ x ∈ (⊤ : Ideal A)
      rw [h]

end IsSimpleRing

namespace IsAzumaya

variable (K A : Type*) [Field K] [Ring A] [Algebra K A]
  [IsSimpleRing A] [Algebra.IsCentral K A]

omit [IsSimpleRing A] [Algebra.IsCentral K A] in
private theorem tensor_smul (a b x : A) :
    (a ⊗ₜ[K] op b) • x = a * x * b := by
  change AlgHom.mulLeftRight K A (a ⊗ₜ[K] op b) x = _
  exact AlgHom.mulLeftRight_apply K A a (op b) x

omit [IsSimpleRing A] in
private theorem bimodule_end_scalar (f : Module.End (A ⊗[K] Aᵐᵒᵖ) A) :
    ∃ k : K, ∀ a : A, f a = k • a := by
  have hl (a : A) : f a = a * f 1 := by
    simpa only [tensor_smul, one_mul, mul_one] using
      f.map_smul (a ⊗ₜ[K] op (1 : A)) (1 : A)
  have hr (a : A) : f a = f 1 * a := by
    simpa only [tensor_smul, one_mul, mul_one] using
      f.map_smul ((1 : A) ⊗ₜ[K] op a) (1 : A)
  have hc : f 1 ∈ Subalgebra.center K A :=
    Subalgebra.mem_center_iff.mpr fun a => (hl a).symm.trans (hr a)
  obtain ⟨k, hk⟩ := (Algebra.IsCentral.mem_center_iff K).mp hc
  refine ⟨k, fun a => ?_⟩
  rw [hr, hk, Algebra.smul_def]

private def doubleEndOfLinearMap (f : Module.End K A) :
    Module.End (Module.End (A ⊗[K] Aᵐᵒᵖ) A) A where
  toFun := f
  map_add' := f.map_add
  map_smul' g a := by
    obtain ⟨k, hk⟩ := bimodule_end_scalar K A g
    change f (g a) = g (f a)
    rw [hk, hk, map_smul]

/-- The original multiplication map is surjective for a finite central simple algebra. -/
theorem mulLeftRight_surjective [FiniteDimensional K A] :
    Function.Surjective (AlgHom.mulLeftRight K A) := by
  classical
  let : IsSimpleModule (A ⊗[K] Aᵐᵒᵖ) A :=
    IsSimpleRing.isSimpleModule_tensor_mulOpposite K A
  let b := Module.finBasis K A
  intro f
  obtain ⟨t, ht⟩ := jacobson_density (doubleEndOfLinearMap K A f) (Finset.univ.image b)
  refine ⟨t, b.ext fun i => ?_⟩
  change t • b i = f (b i)
  exact (ht (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).symm

/-- A finite-dimensional central simple algebra satisfies the native Azumaya condition. -/
theorem of_central_simple [FiniteDimensional K A] : IsAzumaya K A where
  bij := by
    have hdim : Module.finrank K (A ⊗[K] Aᵐᵒᵖ) = Module.finrank K (Module.End K A) := by
      rw [Module.finrank_tensorProduct, MulOpposite.finrank, Module.finrank_linearMap]
    have hs := mulLeftRight_surjective K A
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (AlgHom.mulLeftRight K A).toLinearMap)).mpr hs, hs⟩

end IsAzumaya
