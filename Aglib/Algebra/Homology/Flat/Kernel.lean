/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Flat.UniversalTensor
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Original boundary kernels under arbitrary scalar extension

Universal middle tensor exactness makes the original image and opcycles flat.
The native flat-quotient tensor theorem then preserves the original kernel
inclusion and the image inclusion under every tensor product. Consequently
arbitrary native scalar extension preserves the original boundary kernel,
without requiring the new coefficient ring to be flat.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{v} R))
  [Module.Flat R S.X₂] [Module.Flat R S.X₃]

/-- The actual kernel inclusion remains an injective exact kernel pair after
every module tensor product. Flatness of the original image and opcycles is
proved from universal exactness, rather than supplied independently. -/
theorem kernel_lTensor_exact_and_injective_of_universally_exact
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N))
    (A : Type w) [AddCommGroup A] [Module R A] :
    Function.Exact ((LinearMap.ker S.f.hom).subtype.lTensor A) (S.f.hom.lTensor A) ∧
      Function.Injective ((LinearMap.ker S.f.hom).subtype.lTensor A) := by
  let := S.flat_opcycles_of_universally_lTensor_exact h
  let := S.flat_range_f_of_universally_lTensor_exact h
  have hKR : Function.Exact (LinearMap.ker S.f.hom).subtype S.f.hom.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have hp : Function.Surjective S.pOpcycles.hom :=
    (ModuleCat.epi_iff_surjective S.pOpcycles).mp inferInstance
  let T := ShortComplex.mk S.f S.pOpcycles S.f_pOpcycles
  have he : LinearMap.range S.f.hom = LinearMap.ker S.pOpcycles.hom :=
    (T.exact_of_g_is_cokernel S.opcyclesIsCokernel).moduleCat_range_eq_ker
  have hIR : Function.Exact (LinearMap.range S.f.hom).subtype S.pOpcycles.hom := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, ← he]
  have hI : Function.Injective ((LinearMap.range S.f.hom).subtype.lTensor A) :=
    LinearMap.lTensor_injective_of_exact_of_flat S.pOpcycles.hom hp
      (LinearMap.range S.f.hom).subtype (LinearMap.range S.f.hom).subtype_injective hIR A
  refine ⟨?_, LinearMap.lTensor_injective_of_exact_of_flat S.f.hom.rangeRestrict
    S.f.hom.surjective_rangeRestrict (LinearMap.ker S.f.hom).subtype
      (LinearMap.ker S.f.hom).subtype_injective hKR A⟩
  have H := (_root_.lTensor_exact A hKR S.f.hom.surjective_rangeRestrict).comp_injective
    ((LinearMap.range S.f.hom).subtype.lTensor A) hI (by simp)
  change Function.Exact ((LinearMap.ker S.f.hom).subtype.lTensor A)
    (((LinearMap.range S.f.hom).subtype.lTensor A).comp (S.f.hom.rangeRestrict.lTensor A)) at H
  have hf : (LinearMap.range S.f.hom).subtype.comp S.f.hom.rangeRestrict = S.f.hom := by
    ext x
    rfl
  rw [← LinearMap.lTensor_comp, hf] at H
  exact H

/-- Every native scalar-extension functor preserves the actual kernel of the
first map. No flatness hypothesis on the ring homomorphism is imposed. -/
theorem extendScalars_preservesKernel_of_universally_lTensor_exact
    {B : Type w} [CommRing B] (σ : R →+* B)
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N)) :
    PreservesLimit (parallelPair S.f 0) (ModuleCat.extendScalars.{u, w, v} σ) := by
  let F := ModuleCat.extendScalars.{u, w, v} σ
  have H : Function.Exact
      (F.map (ModuleCat.ofHom (LinearMap.ker S.f.hom).subtype)).hom (F.map S.f).hom ∧
      Function.Injective (F.map (ModuleCat.ofHom (LinearMap.ker S.f.hom).subtype)).hom := by
    algebraize [σ]
    exact S.kernel_lTensor_exact_and_injective_of_universally_exact h B
  apply preservesLimit_of_preserves_limit_cone (ModuleCat.kernelIsLimit S.f)
  refine (KernelFork.isLimitMapConeEquiv (ModuleCat.kernelCone S.f)
    (ModuleCat.extendScalars.{u, w, v} σ)).symm ?_
  exact ModuleCat.isLimitKernelFork
    (F.map (ModuleCat.ofHom (LinearMap.ker S.f.hom).subtype)) (F.map S.f) H.1 H.2

end CategoryTheory.ShortComplex
