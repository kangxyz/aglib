/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Tensor tests for injectivity and cokernel flatness, exact sequences and kernel transport

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 91–155, 239–290, 380–391, 1322–1366.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Module.Flat
variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- If the middle module is flat, injectivity after tensoring the first map
with cyclic quotients implies flatness of the cokernel. -/
theorem flat_of_exact_of_lTensor_quotient_injective [Module.Flat R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hex : Function.Exact f g)
    (hg : Function.Surjective g)
    (hf : ∀ I : Ideal R, Function.Injective (f.lTensor (R ⧸ I))) :
    Module.Flat R P := by
  apply Module.Flat.iff_rTensor_injective'.mpr
  intro I
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  change x = 0
  have hx0 : I.subtype.rTensor P x = 0 := hx
  obtain ⟨y, hy⟩ := lTensor_surjective I hg x
  have hy0 : g.lTensor R (I.subtype.rTensor N y) = 0 := by
    have hc : (g.lTensor R).comp (I.subtype.rTensor N) =
        (I.subtype.rTensor P).comp (g.lTensor I) := by ext; rfl
    simpa only [LinearMap.comp_apply, hy, hx0] using LinearMap.congr_fun hc y
  obtain ⟨z, hz⟩ := (_root_.lTensor_exact R hex hg _).mp hy0
  have hz0 : I.mkQ.rTensor M z = 0 := by
    apply (hf I).eq_iff.mp
    rw [map_zero]
    have hc : (f.lTensor (R ⧸ I)).comp (I.mkQ.rTensor M) =
        (I.mkQ.rTensor N).comp (f.lTensor R) := by ext; rfl
    rw [← LinearMap.comp_apply, hc, LinearMap.comp_apply, hz]
    have he := _root_.rTensor_exact N (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
    exact (he _).mpr ⟨y, rfl⟩
  obtain ⟨w, hw⟩ :=
    (_root_.rTensor_exact M (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective _).mp hz0
  have hyw : y = f.lTensor I w := by
    apply Module.Flat.rTensor_preserves_injective_linearMap I.subtype I.injective_subtype
    rw [← hz, ← hw]
    have hc : (f.lTensor R).comp (I.subtype.rTensor M) =
        (I.subtype.rTensor N).comp (f.lTensor I) := by ext; rfl
    exact LinearMap.congr_fun hc w
  rw [hyw] at hy
  have hzero := (_root_.lTensor_exact I hex hg (f.lTensor I w)).mpr ⟨w, rfl⟩
  exact hy.symm.trans hzero

theorem injective_of_lTensor_quotient_injective (f : M →ₗ[R] N)
    (hf : ∀ I : Ideal R, Function.Injective (f.lTensor (R ⧸ I))) :
    Function.Injective f := by
  intro x y hxy
  have h : (1 : R ⧸ (⊥ : Ideal R)) ⊗ₜ[R] x = 1 ⊗ₜ[R] y :=
    hf ⊥ (by simp only [LinearMap.lTensor_tmul, hxy])
  have h' := congrArg (TensorProduct.quotTensorEquivQuotSMul M (⊥ : Ideal R)) h
  simpa [Submodule.Quotient.eq, sub_eq_zero] using h'

theorem injective_and_flat_iff_lTensor_quotient_injective [Module.Flat R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hex : Function.Exact f g)
    (hg : Function.Surjective g) :
    (Function.Injective f ∧ Module.Flat R P) ↔
      ∀ I : Ideal R, Function.Injective (f.lTensor (R ⧸ I)) := by
  constructor
  · rintro ⟨hf, hp⟩ I
    let := hp
    exact LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hex (R ⧸ I)
  · intro hf
    exact ⟨injective_of_lTensor_quotient_injective f hf,
      flat_of_exact_of_lTensor_quotient_injective f g hex hg hf⟩

theorem lTensor_injective_of_baseChange_injective
    (K Q : Type*) [CommRing K] [Algebra R K] [AddCommGroup Q]
    [Module R Q] [Module K Q] [IsScalarTower R K Q] [Module.Flat K Q]
    (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor K)) :
    Function.Injective (f.lTensor Q) := by
  let eM := AlgebraTensorModule.cancelBaseChange R K K Q M
  let eN := AlgebraTensorModule.cancelBaseChange R K K Q N
  have h : Function.Injective ((f.baseChange K).lTensor Q) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hf
  have hc : ((f.baseChange K).lTensor Q).comp eM.symm.toLinearMap =
      eN.symm.toLinearMap.comp (AlgebraTensorModule.lTensor K Q f) := by
    apply LinearMap.restrictScalars_injective R
    apply TensorProduct.ext'
    intro q m
    rfl
  intro x y hxy
  apply eM.symm.injective
  apply h
  have hx := LinearMap.congr_fun hc x
  have hy := LinearMap.congr_fun hc y
  exact hx.trans ((congrArg eN.symm hxy).trans hy.symm)

theorem lTensor_injective_of_exact [Module.Flat R N]
    (f : M →ₗ[R] N) {Q₁ Q₂ Q₃ : Type*}
    [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₂] [Module R Q₂]
    [AddCommGroup Q₃] [Module R Q₃]
    (i : Q₁ →ₗ[R] Q₂) (p : Q₂ →ₗ[R] Q₃) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p)
    (h₁ : Function.Injective (f.lTensor Q₁))
    (h₃ : Function.Injective (f.lTensor Q₃)) : Function.Injective (f.lTensor Q₂) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  change x = 0
  have hx0 : f.lTensor Q₂ x = 0 := hx
  have hpx : p.rTensor M x = 0 := by
    apply h₃
    rw [map_zero]
    have hc : (f.lTensor Q₃).comp (p.rTensor M) =
        (p.rTensor N).comp (f.lTensor Q₂) := by ext; rfl
    simpa only [LinearMap.comp_apply, hx0, map_zero] using LinearMap.congr_fun hc x
  obtain ⟨y, hy⟩ := (_root_.rTensor_exact M hex hp x).mp hpx
  have hfy : f.lTensor Q₁ y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap i hi
    rw [map_zero]
    have hc : (i.rTensor N).comp (f.lTensor Q₁) =
        (f.lTensor Q₂).comp (i.rTensor M) := by ext; rfl
    simpa only [LinearMap.comp_apply, hy, hx0] using LinearMap.congr_fun hc y
  have hy0 := h₁ (hfy.trans (map_zero _).symm)
  simpa [hy0] using hy.symm

theorem lTensor_injective_of_linearEquiv
    {Q K : Type*} [AddCommGroup Q] [Module R Q] [AddCommGroup K] [Module R K]
    (e : Q ≃ₗ[R] K) (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor K)) :
    Function.Injective (f.lTensor Q) := by
  have hc : (f.lTensor K).comp (e.rTensor M).toLinearMap =
      (e.rTensor N).toLinearMap.comp (f.lTensor Q) := by ext; rfl
  intro x y hxy
  apply (e.rTensor M).injective
  apply hf
  exact (LinearMap.congr_fun hc x).trans
    ((congrArg (e.rTensor N) hxy).trans (LinearMap.congr_fun hc y).symm)


end Module.Flat

namespace Algebra.FlatApproximation
section KernelTransport
variable {k K M N P : Type*} [CommRing k] [CommRing K] [Algebra k K]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  [AddCommGroup P] [Module K P]

/-- Killing the old kernel after a flat scalar extension makes the descended
map injective. For residue fields the flatness hypothesis is automatic. This
is the linear-algebra step replacing a vanishing Tor transition. -/
theorem injective_of_kernel_killed_after_baseChange [Module.Flat k K]
    (f : M →ₗ[k] N) (q : K ⊗[k] M →ₗ[K] P)
    (g : P →ₗ[K] K ⊗[k] N) (hq : Function.Surjective q)
    (hcomm : g.comp q = f.baseChange K)
    (hkill : q.comp ((LinearMap.ker f).subtype.baseChange K) = 0) :
    Function.Injective g := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  change x = 0
  obtain ⟨y, rfl⟩ := hq x
  have hy : f.lTensor K y = 0 := by
    change f.baseChange K y = 0
    rw [← hcomm, LinearMap.comp_apply]
    exact hx
  obtain ⟨z, hz⟩ := (Module.Flat.lTensor_exact K (LinearMap.exact_subtype_ker_map f) y).mp hy
  rw [← hz]
  exact LinearMap.congr_fun hkill z

/-- It suffices to kill the original kernel on unit tensors; scalar linearity
then kills its entire scalar extension. -/
theorem kernel_baseChange_killed_of_unit_tensors
    (f : M →ₗ[k] N) (q : K ⊗[k] M →ₗ[K] P)
    (hkill : ∀ x : LinearMap.ker f, q ((1 : K) ⊗ₜ[k] (x : M)) = 0) :
    q.comp ((LinearMap.ker f).subtype.baseChange K) = 0 := by
  apply LinearMap.ext
  intro z
  change q ((LinearMap.ker f).subtype.baseChange K z) = 0
  induction z with
  | tmul c x =>
      change q (c ⊗ₜ[k] (x : M)) = 0
      have hc : c ⊗ₜ[k] (x : M) = c • ((1 : K) ⊗ₜ[k] (x : M)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, hkill, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

end KernelTransport

end Algebra.FlatApproximation
