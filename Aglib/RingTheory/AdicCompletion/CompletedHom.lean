/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Completion of Hom for finite modules

Over a Noetherian ring, completion of the module of linear maps is the module
of linear maps between completions. The proof uses flatness of the completed
ring and the native finite-presentation Hom base-change theorem. It does not
assert the false analogous statement for individual nonflat quotient rings.
The modules lie in the ring universe, as required by the native finite-module
completion theorem; this includes affine sections in the geometric application.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace AdicCompletion

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- Completion commutes with Hom between finite modules over a Noetherian ring.
The comparison is constructed from the original tensor and completion maps. -/
def completedHomEquiv :
    AdicCompletion I (M →ₗ[R] N) ≃ₗ[AdicCompletion I R]
      (AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) := by
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact (ofTensorProductEquivOfFiniteNoetherian I (M →ₗ[R] N)).symm ≪≫ₗ
    (Module.FinitePresentation.isBaseChange_map R M N (AdicCompletion I R)).equiv ≪≫ₗ
    (ofTensorProductEquivOfFiniteNoetherian I M).arrowCongr
      (ofTensorProductEquivOfFiniteNoetherian I N)

/-- On original morphisms and original elements, the completed comparison
is the native completed map. -/
theorem completedHomEquiv_of_apply_of (f : M →ₗ[R] N) (x : M) :
    completedHomEquiv I M N (of I (M →ₗ[R] N) f) (of I M x) = of I N (f x) := by
  simp [completedHomEquiv, IsBaseChange.equiv_tmul]

/-- The forward comparison extends precisely the native map on completions. -/
@[simp]
theorem completedHomEquiv_of (f : M →ₗ[R] N) :
    completedHomEquiv I M N (of I (M →ₗ[R] N) f) = map I f := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (ofTensorProductEquivOfFiniteNoetherian I M).surjective x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a x =>
    simp only [ofTensorProductEquivOfFiniteNoetherian_apply, ofTensorProduct_tmul,
      map_smul, completedHomEquiv_of_apply_of, map_of]

end AdicCompletion
