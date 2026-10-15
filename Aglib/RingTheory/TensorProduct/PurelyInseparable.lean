/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Nilpotent overlap kernels for finite purely inseparable extensions

For any `L`-algebra `B`, the augmentation `B ⊗[K] L → B` is a split
surjection. Its kernel is nil for purely inseparable `L/K` and nilpotent for
finite purely inseparable `L/K`. The latter uses finite generation of the
kernel as a module over `B`, not a Noetherian hypothesis on `B`.

## Extraction basis

Transferred from `R5Lab.RingTheory.Descent.PurelyInseparableTensor` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`b05313682caa392cba7c7500b9aaa26730854a0f8daf6e06b6b769f2ef7d5d7c`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section

open scoped _root_.TensorProduct

namespace Algebra.TensorProduct

universe u v w

section Tensor

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  (B : Type w) [CommRing B] [Algebra K B] [Algebra L B] [IsScalarTower K L B]

/-- Multiplication on the two copies of `L`, after arbitrary base change to
an `L`-algebra `B`. -/
def tensorAugmentation : B ⊗[K] L →ₐ[B] B :=
  (AlgHom.liftEquiv K B L B) (IsScalarTower.toAlgHom K L B)

@[simp] theorem tensorAugmentation_tmul (b : B) (l : L) :
    tensorAugmentation K L B (b ⊗ₜ[K] l) = b * algebraMap L B l := rfl

theorem tensorAugmentation_algebraMap (b : B) :
    tensorAugmentation K L B (algebraMap B (B ⊗[K] L) b) = b :=
  (tensorAugmentation K L B).commutes b

theorem tensorAugmentation_surjective : Function.Surjective (tensorAugmentation K L B) :=
  fun b ↦ ⟨algebraMap B (B ⊗[K] L) b, tensorAugmentation_algebraMap K L B b⟩

variable [IsPurelyInseparable K L]

/-- The overlap augmentation has nil kernel even for an infinite purely
inseparable extension. -/
theorem tensorAugmentation_ker_le_nilradical :
    RingHom.ker (tensorAugmentation K L B).toRingHom ≤ nilradical (B ⊗[K] L) := by
  intro x hx
  rw [mem_nilradical]
  obtain ⟨n, hn, b, hb⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct x
  have hx' : tensorAugmentation K L B x = 0 := hx
  have hb' : b = 0 := by
    calc
      b = tensorAugmentation K L B (algebraMap B (B ⊗[K] L) b) :=
        (tensorAugmentation_algebraMap K L B b).symm
      _ = tensorAugmentation K L B (x ^ n) := congrArg (tensorAugmentation K L B) hb
      _ = 0 := by rw [map_pow, hx', zero_pow (Nat.ne_of_gt hn)]
  exact ⟨n, hb.symm.trans (by rw [hb', map_zero])⟩

variable [Module.Finite K L]

/-- Finite pure inseparability makes the overlap kernel nilpotent over every
`L`-algebra, including non-Noetherian ones. -/
theorem tensorAugmentation_ker_isNilpotent :
    IsNilpotent (RingHom.ker (tensorAugmentation K L B).toRingHom) := by
  have hfg : (RingHom.ker (tensorAugmentation K L B).toRingHom).FG := by
    apply Submodule.FG.of_restrictScalars B
    exact Module.FinitePresentation.fg_ker (tensorAugmentation K L B).toLinearMap
      (tensorAugmentation_surjective K L B)
  exact hfg.isNilpotent_iff_le_nilradical.mpr (tensorAugmentation_ker_le_nilradical K L B)

end Tensor

section Lifting

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

/-- A formally étale algebra has unique lifts across any surjective algebra
map with nilpotent kernel. The map of Hom sets is actual postcomposition. -/
theorem _root_.Algebra.FormallyEtale.formallyEtale_comp_bijective [Algebra.FormallyEtale R A]
    (f : B →ₐ[R] C) (hf : Function.Surjective f)
    (hker : IsNilpotent (RingHom.ker f.toRingHom)) :
    Function.Bijective (fun g : A →ₐ[R] B ↦ f.comp g) := by
  constructor
  · intro g h e
    exact Algebra.FormallyUnramified.lift_unique' f hker g h e
  · intro g
    exact ⟨Algebra.FormallySmooth.liftOfSurjective g f hf hker,
      Algebra.FormallySmooth.comp_liftOfSurjective g f hf hker⟩

end Lifting

end Algebra.TensorProduct
