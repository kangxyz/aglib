/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Closed-residue tensor tests over local algebras

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native proof validation is pending the coordinated build.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open TensorProduct
open LinearMap
open Module
open IsLocalRing

section
namespace IsLocalRing

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- Relative Nakayama for finite modules over a local algebra, without any
Noetherian hypothesis on either ring. -/
theorem subsingleton_of_residue_tensor_subsingleton [Module.Finite S M]
    [Subsingleton ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] M)] : Subsingleton M := by
  have hm (m : M) : m ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
    have h := congrArg (_root_.TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal R))
      (Subsingleton.elim ((1 : R ⧸ IsLocalRing.maximalIdeal R) ⊗ₜ[R] m) 0)
    simpa only [_root_.TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero,
      Submodule.Quotient.mk_eq_zero] using h
  have hle : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≤
      (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M)).restrictScalars R := by
    apply Submodule.smul_le.mpr
    intro r hr m _
    change r • m ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S M)
    rw [← IsScalarTower.algebraMap_smul S r m]
    exact Submodule.smul_mem_smul
      ((IsLocalRing.map_maximalIdeal_le (algebraMap R S)) (Ideal.mem_map_of_mem _ hr))
      (Submodule.mem_top)
  have htop : (⊤ : Submodule S M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal S) ⊤
      Module.Finite.fg_top (fun m _ ↦ hle (hm m)) (by
        rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top])
  have hz (m : M) : m = 0 := by
    have : m ∈ (⊥ : Submodule S M) := htop ▸ Submodule.mem_top
    exact this
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

end IsLocalRing
end

section
namespace LinearMap

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Surjectivity onto a finite module is detected on the closed base fibre of
a local algebra, without a Noetherian hypothesis. -/
theorem surjective_of_residue_surjective (f : M →ₗ[S] N) [Module.Finite S N]
    (hf : Function.Surjective ((f.restrictScalars R).lTensor
      (R ⧸ IsLocalRing.maximalIdeal R))) : Function.Surjective f := by
  let K := R ⧸ IsLocalRing.maximalIdeal R
  let Q := N ⧸ LinearMap.range f
  let q : N →ₗ[R] Q := (LinearMap.range f).mkQ.restrictScalars R
  have hq : Function.Surjective q := Submodule.mkQ_surjective (LinearMap.range f)
  have hcomp : q.comp (f.restrictScalars R) = 0 := by
    ext m
    exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self f m)
  have hzero (z : K ⊗[R] Q) : z = 0 := by
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective K hq z
    obtain ⟨x, rfl⟩ := hf y
    rw [← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_zero, LinearMap.zero_apply]
  have : Subsingleton (K ⊗[R] Q) := ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
  have : Subsingleton Q := _root_.IsLocalRing.subsingleton_of_residue_tensor_subsingleton (R := R)
    (S := S)
  intro n
  have hn : (LinearMap.range f).mkQ n = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero _).mp hn

end LinearMap
end

section
namespace Ideal

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- A generator of the actual ideal module on the closed base fibre lifts to
a principal generator, provided the ideal is finitely generated. -/
theorem ideal_eq_span_of_residue_generator (I : Ideal S) (hI : I.FG) (a : I)
    (ha : Function.Surjective
      (((LinearMap.toSpanSingleton S I a).restrictScalars R).lTensor
        (R ⧸ IsLocalRing.maximalIdeal R))) : I = Ideal.span {(a : S)} := by
  have : Module.Finite S I := Module.Finite.of_fg hI
  have hs := _root_.LinearMap.surjective_of_residue_surjective (R := R) (LinearMap.toSpanSingleton S
    I a) ha
  apply le_antisymm
  · intro x hx
    obtain ⟨s, he⟩ := hs ⟨x, hx⟩
    have hv := congrArg Subtype.val he
    change s * (a : S) = x at hv
    rw [← hv]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr a.property)

end Ideal
end

section
namespace LinearMap

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- A surjection with finite kernel and base-flat quotient is injective if it is
injective on the closed base fibre. No Noetherian assumption is used. -/
theorem injective_of_surjective_of_flat_quotient_of_residue_injective
    (f : M →ₗ[S] N) [Module.Finite S (LinearMap.ker f)] [Module.Flat R N]
    (hsurj : Function.Surjective f)
    (hf : Function.Injective ((f.restrictScalars R).lTensor
      (R ⧸ IsLocalRing.maximalIdeal R))) : Function.Injective f := by
  let K := R ⧸ IsLocalRing.maximalIdeal R
  let g := f.restrictScalars R
  let e := LinearMap.kerLTensorEquivOfSurjective g hsurj K
  have : Subsingleton (LinearMap.ker (g.lTensor K)) := ⟨fun x y ↦ Subtype.ext <| hf <| by
    rw [show g.lTensor K x = 0 from x.property, show g.lTensor K y = 0 from y.property]⟩
  have : Subsingleton (K ⊗[R] LinearMap.ker f) :=
    ⟨fun x y ↦ e.symm.injective (Subsingleton.elim _ _)⟩
  have : Subsingleton (LinearMap.ker f) :=
    _root_.IsLocalRing.subsingleton_of_residue_tensor_subsingleton
    (R := R) (S := S)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  have hzero : (⟨x, hx⟩ : LinearMap.ker f) = 0 := Subsingleton.elim _ _
  exact congrArg Subtype.val hzero

end LinearMap
end

section
namespace Algebra

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra.FinitePresentation R S] [Algebra.FinitePresentation R T] [Module.Flat R T]

/-- A finitely presented quotient that is flat over the local base agrees with
the source as soon as their closed fibres agree. This applies over arbitrary
non-Noetherian local bases. -/
theorem bijective_of_surjective_of_residue_injective
    (hsurj : Function.Surjective (algebraMap S T))
    (hf : Function.Injective ((IsScalarTower.toAlgHom R S T).toLinearMap.lTensor
      (R ⧸ IsLocalRing.maximalIdeal R))) : Function.Bijective (algebraMap S T) := by
  have hfg : (RingHom.ker (algebraMap S T)).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (IsScalarTower.toAlgHom R S T) hsurj
  have : Module.Finite S (LinearMap.ker (Algebra.linearMap S T)) := Module.Finite.of_fg hfg
  exact ⟨_root_.LinearMap.injective_of_surjective_of_flat_quotient_of_residue_injective
    (R := R) (S := S) (Algebra.linearMap S T) hsurj hf, hsurj⟩

end Algebra
end

section
namespace IsLocalRing

/-- A rank-one residue basis of a finite module over a local ring lifts to a
single generator; freeness of the module is not assumed. -/
theorem exists_surjective_unit_of_residue_basis
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [IsLocalRing R] [Module.Finite R M]
    (b : Module.Basis PUnit (IsLocalRing.ResidueField R)
      ((IsLocalRing.ResidueField R) ⊗[R] M)) :
    ∃ f : R →ₗ[R] M, Function.Surjective f := by
  obtain ⟨a, ha⟩ := _root_.TensorProduct.mk_surjective R M (IsLocalRing.ResidueField R)
    Ideal.Quotient.mk_surjective (b PUnit.unit)
  refine ⟨LinearMap.toSpanSingleton R M a, ?_⟩
  apply LinearMap.range_eq_top.mp
  rw [LinearMap.range_toSpanSingleton]
  have hb := IsLocalRing.span_eq_top_of_tmul_eq_basis (fun _ : PUnit ↦ a) b
    (fun j ↦ by cases j; exact ha)
  simpa only [Set.range_const] using hb

end IsLocalRing
end
