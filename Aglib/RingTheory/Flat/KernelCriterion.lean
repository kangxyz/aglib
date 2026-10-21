/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, kangxyz
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Flatness and tensor injectivity over a quotient kernel

The restricted tensor criterion uses a surjective base map and its actual kernel.
It applies to injections whose cokernel is annihilated by that kernel. The ideal
criterion then detects flatness from quotient flatness and tensor injections
for ideals contained in the kernel, without a nilpotence or local-ring premise.

The presentation diagram generalizes the argument in
`Mathlib.RingTheory.Flat.Equalizer`, retaining the original attribution.
Additional copyright: Copyright (c) 2026 kangxyz. All rights reserved.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Module.Flat

private theorem lTensor_injective_of_exact_of_presentation
    {R X Y Z A F : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] [AddCommGroup A] [Module R A]
    [AddCommGroup F] [Module R F] [Module.Flat R F]
    (f : Y →ₗ[R] Z) (hf : Function.Surjective f)
    (g : X →ₗ[R] Y) (hg : Function.Injective g) (H : Function.Exact g f)
    (π : F →ₗ[R] A) (hπ : Function.Surjective π)
    (h : Function.Injective ((LinearMap.ker π).subtype.rTensor Z)) :
    Function.Injective (g.lTensor A) := by
  let K := LinearMap.ker π
  have hsnake := SnakeLemma.exact_δ'_left
    (K.subtype.rTensor X) (K.subtype.rTensor Y) (K.subtype.rTensor Z)
    (g.lTensor K) (f.lTensor K) (_root_.lTensor_exact K H hf)
    (g.lTensor F) (f.lTensor F) (_root_.lTensor_exact F H hf)
    (by simp) (by simp) (K₃ := Unit) 0 (by simpa using h)
    (π.rTensor X) (_root_.rTensor_exact _ (LinearMap.exact_subtype_ker_map π) hπ)
    (π.rTensor Y) (_root_.rTensor_exact _ (LinearMap.exact_subtype_ker_map π) hπ)
    (LinearMap.lTensor_surjective K hf)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hg) (g.lTensor A)
    (by simp) (LinearMap.rTensor_surjective _ hπ)
  rw [Subsingleton.elim (SnakeLemma.δ' ..) 0] at hsnake
  simpa using hsnake

private theorem rTensor_injective_of_flat_baseChange_of_quotient_cokernel_of_presentation
    {R S M A B N F : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat S (S ⊗[R] M)]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommGroup F] [Module R F] [Module.Flat R F]
    (π : F →ₗ[R] M) (hπ : Function.Surjective π)
    (hS : Function.Surjective (algebraMap R S))
    (hJ : Function.Injective ((LinearMap.ker (Algebra.linearMap R S)).subtype.rTensor M))
    (f : A →ₗ[R] B) (g : B →ₗ[R] N)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Injective (f.rTensor M) := by
  let K := LinearMap.ker π
  let iS := K.subtype.baseChange S
  let πS := π.baseChange S
  have hiS : Function.Injective iS := by
    change Function.Injective (K.subtype.lTensor S)
    exact lTensor_injective_of_exact_of_presentation
      (R := R) (X := K) (Y := F) (Z := M) (A := S) (F := R) π hπ K.subtype
      K.subtype_injective (LinearMap.exact_subtype_ker_map π)
      (Algebra.linearMap R S) hS hJ
  have hπS : Function.Surjective πS := LinearMap.baseChange_surjective S hπ
  have hexS : Function.Exact iS πS :=
    _root_.lTensor_exact S (LinearMap.exact_subtype_ker_map π) hπ
  have hNS : Function.Injective (iS.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat πS hπS iS hiS hexS N
  have hnat (z : N ⊗[R] K) :
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N F
        (iS.lTensor N
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N K).symm z)) =
        K.subtype.lTensor N z := by
    induction z using TensorProduct.inductionOn with
    | tmul n k => simp [iS]
    | add x y ihx ihy => simp only [map_add, ihx, ihy]
  have hN : Function.Injective (K.subtype.lTensor N) := by
    intro x y hxy
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N K).symm.injective
    apply hNS
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N F).injective
    exact (hnat x).trans (hxy.trans (hnat y).symm)
  have hNr : Function.Injective (K.subtype.rTensor N) := by
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact hN
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  exact lTensor_injective_of_exact_of_presentation
    (R := R) (X := A) (Y := B) (Z := N) (A := M) (F := F) g hg f hf hfg π hπ hNr

/-- Let `R → S` be surjective. If `S ⊗[R] M` is `S`-flat and tensoring the
original kernel inclusion with `M` is injective, tensoring with `M` preserves
injections whose cokernel has a compatible `S`-module structure. Thus the
cokernel is annihilated by the original kernel. No nilpotence, finiteness,
or Noetherian hypothesis is imposed. -/
theorem rTensor_injective_of_flat_baseChange_of_quotient_cokernel
    {R S M A B N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat S (S ⊗[R] M)]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (hS : Function.Surjective (algebraMap R S))
    (hJ : Function.Injective ((LinearMap.ker (Algebra.linearMap R S)).subtype.rTensor M))
    (f : A →ₗ[R] B) (g : B →ₗ[R] N)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Injective (f.rTensor M) := by
  let F := M →₀ R
  let π : F →ₗ[R] M := Finsupp.linearCombination R fun m => m
  have hπ : Function.Surjective π :=
    Finsupp.linearCombination_surjective _ Function.surjective_id
  exact rTensor_injective_of_flat_baseChange_of_quotient_cokernel_of_presentation
    π hπ hS hJ f g hf hfg hg

/-- Explicit annihilation version of the quotient-cokernel tensor criterion.
The quotient action is constructed from the original surjection. -/
theorem rTensor_injective_of_flat_baseChange_of_annihilated_cokernel
    {R S M A B N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat S (S ⊗[R] M)]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup N] [Module R N]
    (hS : Function.Surjective (algebraMap R S))
    (hJ : Function.Injective ((LinearMap.ker (Algebra.linearMap R S)).subtype.rTensor M))
    (hN : ∀ r ∈ RingHom.ker (algebraMap R S), ∀ n : N, r • n = 0)
    (f : A →ₗ[R] B) (g : B →ₗ[R] N)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Injective (f.rTensor M) := by
  let c : S → R := fun s => Classical.choose (hS s)
  have hc (s : S) : algebraMap R S (c s) = s := Classical.choose_spec (hS s)
  let : SMul S N := ⟨fun s n => c s • n⟩
  have hsmul (r : R) (n : N) : algebraMap R S r • n = r • n := by
    change c (algebraMap R S r) • n = r • n
    apply sub_eq_zero.mp
    rw [← sub_smul]
    have hmem : c (algebraMap R S r) - r ∈ RingHom.ker (algebraMap R S) := by
      change algebraMap R S (c (algebraMap R S r) - r) = 0
      rw [map_sub, hc, sub_self]
    exact hN _ hmem n
  let : Module S N := Function.Surjective.moduleLeft (algebraMap R S) hS hsmul
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul hsmul
  exact rTensor_injective_of_flat_baseChange_of_quotient_cokernel hS hJ f g hf hfg hg

/-- Flatness after base change preserves tensor injections between modules
already carrying the compatible larger-ring actions. -/
theorem rTensor_injective_of_flat_baseChange
    {R S M A B : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat S (S ⊗[R] M)]
    [AddCommGroup A] [Module R A] [Module S A] [IsScalarTower R S A]
    [AddCommGroup B] [Module R B] [Module S B] [IsScalarTower R S B]
    (f : A →ₗ[S] B) (hf : Function.Injective f) :
    Function.Injective ((f.restrictScalars R).rTensor M) := by
  let eA := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S A M
  let eB := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S B M
  have hnat (x : A ⊗[R] M) :
      eB (f.rTensor (S ⊗[R] M) (eA.symm x)) = (f.restrictScalars R).rTensor M x := by
    induction x using TensorProduct.inductionOn with
    | tmul a m => simp [eA, eB]
    | add x y ihx ihy => simp only [map_add, ihx, ihy]
  intro x y hxy
  apply eA.symm.injective
  apply Module.Flat.rTensor_preserves_injective_linearMap f hf
  apply eB.injective
  exact (hnat x).trans (hxy.trans (hnat y).symm)

/-- Flatness reduces to tensor injections for ideals contained in the kernel
of a surjection, provided that the quotient base change is flat. -/
theorem of_ideal_rTensor_injective_below_kernel
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat S (S ⊗[R] M)]
    (hS : Function.Surjective (algebraMap R S))
    (hker : ∀ I : Ideal R, I ≤ RingHom.ker (algebraMap R S) →
      Function.Injective (I.subtype.rTensor M)) : Module.Flat R M := by
  apply Module.Flat.iff_rTensor_injective'.mpr
  intro I
  let J := RingHom.ker (algebraMap R S)
  let K := I ⊓ J
  let L := I.map (algebraMap R S)
  let : IsScalarTower R S L := ⟨fun r s x => Subtype.ext (smul_assoc r s x.val)⟩
  let rho : I →ₗ[R] L :=
    { toFun := fun x => ⟨algebraMap R S x, Ideal.mem_map_of_mem _ x.property⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun r x => by
        apply Subtype.ext
        change algebraMap R S (r * x.val) = r • algebraMap R S x.val
        rw [map_mul, Algebra.smul_def] }
  have hrho : Function.Surjective rho := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (Ideal.mem_map_iff_of_surjective (algebraMap R S) hS).mp y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let i : K →ₗ[R] I := Submodule.inclusion inf_le_left
  have hex : Function.Exact i rho := by
    intro x
    constructor
    · intro hx
      have hx0 : algebraMap R S x = 0 := congrArg Subtype.val hx
      exact ⟨⟨x.val, x.property, hx0⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext x.property.2
  have hL : Function.Injective ((L.subtype.restrictScalars R).rTensor M) :=
    rTensor_injective_of_flat_baseChange L.subtype L.subtype_injective
  have hcomm : (L.subtype.restrictScalars R).comp rho =
      (Algebra.linearMap R S).comp I.subtype := rfl
  have hzero (x : I ⊗[R] M) (hx : I.subtype.rTensor M x = 0) : x = 0 := by
    have hrhox : rho.rTensor M x = 0 := by
      apply hL
      rw [map_zero, ← LinearMap.rTensor_comp_apply, hcomm,
        LinearMap.rTensor_comp_apply, hx, map_zero]
    obtain ⟨y, hy⟩ := (_root_.rTensor_exact M hex hrho x).mp hrhox
    have hy0 : K.subtype.rTensor M y = 0 := by
      have hcomp : K.subtype = I.subtype.comp i := rfl
      rw [hcomp, LinearMap.rTensor_comp_apply, hy, hx]
    have hy' : y = 0 := hker K inf_le_right (hy0.trans (map_zero _).symm)
    simpa only [hy', map_zero] using hy.symm
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hxy, sub_self]

end Module.Flat
