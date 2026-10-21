/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.QuotientTower

/-!
# Long-exact-sequence bounds for the actual quotient tower

This leaf isolates the conditional long-exact-sequence step. Killing the next-degree
kernel under a coefficient transition forces its quotient-cohomology image to lift
from the original coefficient. The kernel-killing hypothesis must be supplied by
Rees stabilization; it is not claimed as a consequence of finite cohomology alone.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) (F : X.Modules) (I : Ideal A)

/-- The next-degree kernel-killing estimate implies lifting along the original reduction. -/
theorem idealPowerQuotientMap_mem_range_of_kernel_killed {n m : ℕ} (h : n ≤ m) (p : ℕ)
    (hkill : ∀ z : Sheaf.H.{u + 1} (moduleAddSheaf X (idealPower X α F I m)) (p + 1),
      moduleCohomologyMapOfHom X α (idealMultipleι X α F (I ^ m)) (p + 1) z = 0 →
      moduleCohomologyMapOfHom X α (idealPowerMap X α F I h) (p + 1) z = 0)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (idealPowerQuotient X α F I m)) p) :
    moduleCohomologyMapOfHom X α (idealPowerQuotientMap X α F I h) p x ∈
      Set.range (moduleCohomologyMapOfHom X α (idealQuotientπ X α F (I ^ n)) p) := by
  apply (moduleCohomologyConnectingOfHom_exact_left X α (idealSequence X α F (I ^ n))
    (idealSequence_shortExact X α F (I ^ n)) p _).mp
  rw [idealPowerQuotient_connecting_naturality X α F I h p x]
  apply hkill
  exact (moduleCohomologyConnectingOfHom_exact_right X α (idealSequence X α F (I ^ m))
    (idealSequence_shortExact X α F (I ^ m)) p).apply_apply_eq_zero x

/-- The `n`th ideal multiple of original cohomology lies in the kernel of reduction. -/
theorem idealPowerQuotientReduction_pow_le_ker (n p : ℕ) :
    letI := moduleCohomologyModuleOfHom X α F p
    letI := moduleCohomologyModuleOfHom X α (idealPowerQuotient X α F I n) p
    (I ^ n) • (⊤ : Submodule A (Sheaf.H.{u + 1} (moduleAddSheaf X F) p)) ≤
      (moduleCohomologyMapOfHom X α (idealQuotientπ X α F (I ^ n)) p).ker := by
  let := moduleCohomologyModuleOfHom X α F p
  let := moduleCohomologyModuleOfHom X α (idealPowerQuotient X α F I n) p
  apply Submodule.smul_le.mpr
  intro a ha x _
  change moduleCohomologyMapOfHom X α (idealQuotientπ X α F (I ^ n)) p (a • x) = 0
  rw [_root_.map_smul]
  exact idealPowerQuotientCohomology_smul_eq_zero X α F I n p ⟨a, ha⟩ _

/-- The image estimate in degree `p` is precisely the upper kernel bound for reduction. -/
theorem idealPowerQuotientReduction_ker_le_of_image_le (n m p : ℕ)
    (himage : letI := moduleCohomologyModuleOfHom X α F p
      letI := moduleCohomologyModuleOfHom X α (idealPower X α F I m) p
      (moduleCohomologyMapOfHom X α (idealMultipleι X α F (I ^ m)) p).range ≤
        (I ^ n) • (⊤ : Submodule A (Sheaf.H.{u + 1} (moduleAddSheaf X F) p))) :
    letI := moduleCohomologyModuleOfHom X α F p
    letI := moduleCohomologyModuleOfHom X α (idealPowerQuotient X α F I m) p
    (moduleCohomologyMapOfHom X α (idealQuotientπ X α F (I ^ m)) p).ker ≤
      (I ^ n) • (⊤ : Submodule A (Sheaf.H.{u + 1} (moduleAddSheaf X F) p)) := by
  let := moduleCohomologyModuleOfHom X α F p
  let := moduleCohomologyModuleOfHom X α (idealPower X α F I m) p
  let := moduleCohomologyModuleOfHom X α (idealPowerQuotient X α F I m) p
  intro x hx
  apply himage
  exact (moduleCohomologyMapOfHom_exact X α (idealSequence X α F (I ^ m))
    (idealSequence_shortExact X α F (I ^ m)) p x).mp hx

end AlgebraicGeometry.Scheme.Cohomology
