/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization and finite defects of tensor-dual evaluation

The actual rank-one endomorphism map has finite-length kernel and cokernel
for a finite module over a Noetherian local ring which is free off the closed
point. No regularity or reflexivity assumption is used.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace Module

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The rank-one endomorphism associated to a vector and a linear functional. -/
def tensorDualEvaluation : M ⊗[R] Dual R M →ₗ[R] Module.End R M :=
  (dualTensorHom R M M).comp (TensorProduct.comm R M (Dual R M)).toLinearMap

@[simp]
theorem tensorDualEvaluation_tmul (m x : M) (f : Dual R M) :
    tensorDualEvaluation R M (m ⊗ₜ[R] f) x = f x • m := rfl

/-- Finite free tensor-dual evaluation is bijective. -/
theorem tensorDualEvaluation_bijective [Module.Finite R M] [Free R M] :
    Function.Bijective (tensorDualEvaluation R M) :=
  (dualTensorHomEquiv R M M).bijective.comp (TensorProduct.comm R M (Dual R M)).bijective

variable {R M}

/-- Localization of the actual evaluation is bijective when the localized module is free. -/
theorem tensorDualEvaluation_localized_bijective [FinitePresentation R M]
    (S : Submonoid R) [Free (Localization S) (LocalizedModule S M)] :
    Function.Bijective (LocalizedModule.map S (tensorDualEvaluation R M)) := by
  let A := Localization S
  let N := LocalizedModule S M
  let f : M →ₗ[R] N := LocalizedModule.mkLinearMap S M
  let d : Dual R M →ₗ[R] Dual A N :=
    IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R A) A
  let h : Module.End R M →ₗ[R] Module.End A N :=
    IsLocalizedModule.mapExtendScalars S f f A
  let t : M ⊗[R] Dual R M →ₗ[R] N ⊗[R] Dual A N := TensorProduct.map f d
  let e : N ⊗[R] Dual A N →ₗ[R] Module.End A N :=
    ((tensorDualEvaluation A N).comp
      (IsLocalization.moduleTensorEquiv S A N (Dual A N)).symm.toLinearMap).restrictScalars R
  have he : Function.Bijective e :=
    (tensorDualEvaluation_bijective A N).comp
      (IsLocalization.moduleTensorEquiv S A N (Dual A N)).symm.bijective
  have hsquare : e.comp t = h.comp (tensorDualEvaluation R M) := by
    apply TensorProduct.ext'
    intro m l
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext S f f
    ext x
    change d l (f x) • f m =
      IsLocalizedModule.map S f f (tensorDualEvaluation R M (m ⊗ₜ[R] l)) (f x)
    rw [IsLocalizedModule.map_apply]
    change IsLocalizedModule.map S f (Algebra.linearMap R A) l (f x) • f m = _
    rw [IsLocalizedModule.map_apply]
    simp [tensorDualEvaluation_tmul, ← algebraMap_smul A]
  let a := IsLocalizedModule.linearEquiv S
    (LocalizedModule.mkLinearMap S (M ⊗[R] Dual R M)) t
  let b := IsLocalizedModule.linearEquiv S
    (LocalizedModule.mkLinearMap S (Module.End R M)) h
  have hmap : (LocalizedModule.map S (tensorDualEvaluation R M)).restrictScalars R =
      b.symm.toLinearMap.comp (e.comp a.toLinearMap) := by
    apply IsLocalizedModule.linearMap_ext S
      (LocalizedModule.mkLinearMap S (M ⊗[R] Dual R M))
      (LocalizedModule.mkLinearMap S (Module.End R M))
    apply LinearMap.ext
    intro z
    apply b.injective
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk]
    change b (LocalizedModule.mk (tensorDualEvaluation R M z) 1) =
      e (a (LocalizedModule.mk z 1))
    rw [show a (LocalizedModule.mk z 1) = t z from
      IsLocalizedModule.linearEquiv_apply S _ _ z]
    rw [show b (LocalizedModule.mk (tensorDualEvaluation R M z) 1) =
      h (tensorDualEvaluation R M z) from
      IsLocalizedModule.linearEquiv_apply S _ _ (tensorDualEvaluation R M z)]
    exact (LinearMap.congr_fun hsquare z).symm
  change Function.Bijective
    ((LocalizedModule.map S (tensorDualEvaluation R M)).restrictScalars R)
  rw [hmap]
  exact b.symm.bijective.comp (he.comp a.bijective)

end Module
