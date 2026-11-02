/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms


/-!
# The scaled inverse produced by the actual one-pole image bound

A scalar image bound for the original raw coefficient map constructs a
scaled inverse into the target line whenever the original kernel is killed.
The construction uses the native quotient-range equivalence, not arbitrary
preimage choices. An injective generic target and its original square derive
the kernel condition and the exact scaled generic normalization.
-/

@[expose] public noncomputable section

universe u

namespace LinearMap

variable {R P M N V : Type u} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup V] [Module R V]
  (f : P →ₗ[R] M) (g : P →ₗ[R] N) (x : R)
  (hbound : ∀ m : M, x • m ∈ range f) (hker : ker f ≤ ker g)

/-- The original scalar image bound followed by the original quotient-range inverse. -/
def scaledImageLift : M →ₗ[R] N :=
  ((ker f).liftQ g hker).comp
    (f.quotKerEquivRange.symm.toLinearMap.comp
      ((x • LinearMap.id).codRestrict (range f) hbound))

/-- Every original witness of the scaled image gives the same constructed value. -/
theorem scaledImageLift_apply_of_image (m : M) (p : P) (hp : f p = x • m) :
    scaledImageLift f g x hbound hker m = g p := by
  have he : (⟨x • m, hbound m⟩ : range f) = ⟨f p, ⟨p, rfl⟩⟩ :=
    Subtype.ext hp.symm
  change (ker f).liftQ g hker (f.quotKerEquivRange.symm ⟨x • m, hbound m⟩) = _
  rw [he]
  exact congrArg ((ker f).liftQ g hker)
    (f.quotKerEquivRange_symm_apply_image p ⟨p, rfl⟩)

/-- The constructed scaled inverse has its exact original coefficient value. -/
theorem scaledImageLift_comp_apply (p : P) :
    scaledImageLift f g x hbound hker (f p) = x • g p := by
  exact (scaledImageLift_apply_of_image f g x hbound hker (f p) (x • p)
    (f.map_smul x p)).trans (g.map_smul x p)

/-- An original generic square into an injective target embedding kills the
kernel of the actual raw coefficient map. -/
theorem ker_le_ker_of_injective_generic_square
    (i : N →ₗ[R] V) (j : M →ₗ[R] V) (hi : Function.Injective i)
    (hsq : i.comp g = j.comp f) : ker f ≤ ker g := by
  intro p hp
  apply hi
  have he := LinearMap.congr_fun hsq p
  change i (g p) = j (f p) at he
  change i (g p) = i 0
  rw [mem_ker.mp hp, map_zero] at he
  exact he.trans (map_zero i).symm

/-- The scaled lift retains the exact original generic value, not an
unspecified nonzero scalar multiple. -/
theorem scaledImageLift_generic
    (i : N →ₗ[R] V) (j : M →ₗ[R] V) (hsq : i.comp g = j.comp f) (m : M) :
    i (scaledImageLift f g x hbound hker m) = x • j m := by
  obtain ⟨p, hp⟩ := hbound m
  rw [scaledImageLift_apply_of_image f g x hbound hker m p hp]
  exact (LinearMap.congr_fun hsq p).trans
    ((congrArg j hp).trans (j.map_smul x m))

end LinearMap
