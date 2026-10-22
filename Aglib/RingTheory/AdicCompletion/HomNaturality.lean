/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompletedHom

/-! # Naturality of the completed Hom comparison -/

@[expose] public section

noncomputable section

namespace AdicCompletion

universe u v
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {P : Type v} [AddCommGroup P] [Module (AdicCompletion I R) P]

/-- Maps linear over the completed ring are determined by original elements
of a finite module. The target need not be finite or complete. -/
theorem linearMap_ext_of_finite {f g : AdicCompletion I M →ₗ[AdicCompletion I R] P}
    (h : ∀ x : M, f (of I M x) = g (of I M x)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (ofTensorProductEquivOfFiniteNoetherian I M).surjective x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a x =>
    simp only [ofTensorProductEquivOfFiniteNoetherian_apply, ofTensorProduct_tmul, map_smul, h]

variable {N Q : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
  [AddCommGroup Q] [Module R Q] [Module.Finite R Q]

/-- Completed Hom comparison commutes with precomposition by an original map. -/
theorem completedHomEquiv_precomp (f : M →ₗ[R] N) :
    (completedHomEquiv I M Q).toLinearMap ∘ₗ map I (LinearMap.lcomp R Q f) =
      (LinearMap.lcomp (AdicCompletion I R) (AdicCompletion I Q) (map I f)) ∘ₗ
        (completedHomEquiv I N Q).toLinearMap := by
  apply linearMap_ext_of_finite I
  intro g
  simp only [LinearMap.comp_apply, map_of, LinearEquiv.coe_coe, completedHomEquiv_of,
    LinearMap.lcomp_apply']
  exact (map_comp I f g).symm

/-- Completed Hom comparison commutes with postcomposition by an original map. -/
theorem completedHomEquiv_postcomp (g : N →ₗ[R] Q) :
    (completedHomEquiv I M Q).toLinearMap ∘ₗ map I (LinearMap.compRight R g (M := M)) =
      (LinearMap.compRight (AdicCompletion I R) (map I g) (M := AdicCompletion I M)) ∘ₗ
        (completedHomEquiv I M N).toLinearMap := by
  apply linearMap_ext_of_finite I
  intro f
  simp only [LinearMap.comp_apply, map_of, LinearEquiv.coe_coe, completedHomEquiv_of]
  exact (map_comp I f g).symm

end AdicCompletion
