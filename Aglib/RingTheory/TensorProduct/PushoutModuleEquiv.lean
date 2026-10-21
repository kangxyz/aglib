/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.IsTensorProduct

/-! # Promoting an original module base-change equivalence across an algebra pushout -/

@[expose] public noncomputable section

open scoped TensorProduct
namespace Algebra.IsPushout

variable (R S C D : Type*) [CommRing R] [CommRing S] [CommRing C] [CommRing D]
  [Algebra R S] [Algebra R C] [Algebra R D] [Algebra C D] [Algebra S D]
  [IsScalarTower R C D] [IsScalarTower R S D] [Algebra.IsPushout R S C D]
  {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module C M] [IsScalarTower R C M]
  [Module C N] [Module S N] [Module D N]
  [IsScalarTower C D N] [IsScalarTower S D N]

/-- A coordinate base-change equivalence and an intertwining original map
induce the same equivalence over the full algebra pushout. -/
def moduleEquivOfCoordinateEquiv (f : M →ₗ[C] N)
    (e : S ⊗[R] M ≃ₗ[S] N) (he : ∀ x, e (1 ⊗ₜ[R] x) = f x) :
    D ⊗[C] M ≃ₗ[D] N := by
  let g := f.liftBaseChange D
  let c := Algebra.IsPushout.cancelBaseChange R S C D M
  have hc (z : S ⊗[R] M) : g (c.symm z) = e z := by
    induction z using TensorProduct.inductionOn with
    | tmul s x =>
      rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, LinearMap.liftBaseChange_tmul,
        IsScalarTower.algebraMap_smul D]
      have ht : s ⊗ₜ[R] x = s • ((1 : S) ⊗ₜ[R] x) := by
        rw [TensorProduct.smul_tmul']
        simp
      rw [ht, e.map_smul, he]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hg : (g : D ⊗[C] M → N) = e ∘ c := by
    funext z
    simpa only [LinearEquiv.symm_apply_apply, Function.comp_apply] using hc (c z)
  exact LinearEquiv.ofBijective g (by rw [hg]; exact e.bijective.comp c.bijective)

/-- The promoted map is still the original scalar-extension map on pure tensors. -/
@[simp]
theorem moduleEquivOfCoordinateEquiv_tmul (f : M →ₗ[C] N)
    (e : S ⊗[R] M ≃ₗ[S] N) (he : ∀ x, e (1 ⊗ₜ[R] x) = f x)
    (d : D) (x : M) :
    moduleEquivOfCoordinateEquiv R S C D f e he (d ⊗ₜ[C] x) = d • f x := rfl

end Algebra.IsPushout
