/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.DiagonalLocalization

/-! # Transport of the selected separable centre ideal

For an actual surjection onto the separable tensor residue algebra, the kernel
becomes the entire centre maximal ideal after localization at the selected
diagonal point. Denominators are lifted through the actual surjection.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace SeparableTensorDiagonal

variable (k E : Type*) [Field k] [Field E] [Algebra k E]
variable {A : Type*} [CommRing A] (f : A →+* E ⊗[k] E)

/-- The actual source prime selected by multiplication after the residue quotient map. -/
abbrev sourceIdeal : Ideal A :=
  RingHom.ker ((Algebra.TensorProduct.lmul'' k : E ⊗[k] E →ₐ[E] E).toRingHom.comp f)

instance sourceIdeal_isPrime : (sourceIdeal k E f).IsPrime :=
  RingHom.ker_isPrime
    ((Algebra.TensorProduct.lmul'' k : E ⊗[k] E →ₐ[E] E).toRingHom.comp f)

/-- The source localized at the actual selected component. -/
abbrev SourceRing := Localization.AtPrime (sourceIdeal k E f)

/-- The actual selected residue point extends across the source localization. -/
def sourcePoint : SourceRing k E f →+* E :=
  IsLocalization.lift (M := (sourceIdeal k E f).primeCompl)
    (g := (Algebra.TensorProduct.lmul'' k : E ⊗[k] E →ₐ[E] E).toRingHom.comp f)
    (fun u => isUnit_iff_ne_zero.mpr u.property)

/-- The lifted source point retains the actual residue quotient and multiplication maps. -/
@[simp] theorem sourcePoint_algebraMap (a : A) :
    sourcePoint k E f (algebraMap A (SourceRing k E f) a) =
      Algebra.TensorProduct.lmul'' k (f a) :=
  IsLocalization.lift_eq _ a

/-- Surjectivity of the residue quotient gives surjectivity of the selected local point. -/
theorem sourcePoint_surjective (hf : Function.Surjective f) :
    Function.Surjective (sourcePoint k E f) := by
  intro x
  obtain ⟨a, ha⟩ := hf (x ⊗ₜ[k] (1 : E))
  refine ⟨algebraMap A (SourceRing k E f) a, ?_⟩
  rw [sourcePoint_algebraMap, ha]
  change x * 1 = x
  exact mul_one x

variable [Module.Finite k E] [Algebra.IsSeparable k E]

/-- The actual residue kernel becomes the centre maximal ideal on the selected local component. -/
theorem map_ker_eq_maximalIdeal (hf : Function.Surjective f) :
    (RingHom.ker f).map (algebraMap A (SourceRing k E f)) =
      IsLocalRing.maximalIdeal (SourceRing k E f) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
    (sourceIdeal k E f) (SourceRing k E f)]
  apply le_antisymm
  · apply Ideal.map_mono
    intro a ha
    change Algebra.TensorProduct.lmul'' k (f a) = 0
    rw [show f a = 0 from ha, map_zero]
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change algebraMap A (SourceRing k E f) a ∈
      (RingHom.ker f).map (algebraMap A (SourceRing k E f))
    have hzero : algebraMap (E ⊗[k] E) (Ring k E) (f a) = 0 := by
      apply point_injective k E
      rw [point_algebraMap, map_zero]
      exact ha
    obtain ⟨t, ht⟩ :=
      (IsLocalization.map_eq_zero_iff (ideal k E).primeCompl (Ring k E) (f a)).mp hzero
    obtain ⟨b, hb⟩ := hf t
    have hbQ : b ∈ (sourceIdeal k E f).primeCompl := by
      intro h
      apply t.property
      change Algebra.TensorProduct.lmul'' k (t : E ⊗[k] E) = 0
      rw [← hb]
      exact h
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (sourceIdeal k E f).primeCompl (SourceRing k E f) (RingHom.ker f) a).mpr
    refine ⟨b, hbQ, ?_⟩
    change f (b * a) = 0
    rw [map_mul, hb]
    exact ht

end SeparableTensorDiagonal
