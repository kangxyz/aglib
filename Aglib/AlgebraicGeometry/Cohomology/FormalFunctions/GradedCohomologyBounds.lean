/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.GradedCohomologyTransition
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.QuotientTowerBounds

/-!
# Bounds from finite original Rees cohomology

These intermediate results assume finite generation of the actual direct sum for
its specified compatible Rees action. The geometric comparison discharges that
hypothesis. They preserve the original coefficient inclusions and transitions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory DirectSum
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) (F : X.Modules) (I : Ideal A) (p : ℕ)
variable [Module (reesAlgebra I) (idealPowerCohomologyTotal X α F I p)]
variable (hact : IdealPowerCohomologyActionCompatible X α F I p)
variable [Module.Finite (reesAlgebra I) (idealPowerCohomologyTotal X α F I p)]

include hact in
/-- Finite Rees cohomology bounds the original inclusion images by shifted ideal powers. -/
theorem idealPowerCohomology_exists_image_bound :
    ∃ c : ℕ, ∀ n, letI := moduleCohomologyModuleOfHom X α F p
      letI := moduleCohomologyModuleOfHom X α (idealPower X α F I (n + c)) p
      (moduleCohomologyMapOfHom X α (idealMultipleι X α F (I ^ (n + c))) p).range ≤
        (I ^ n) • (⊤ : Submodule A (Sheaf.H.{u + 1} (moduleAddSheaf X F) p)) := by
  let := idealPowerCohomology_gradedSMul X α F I p hact
  let T := idealPowerCohomologyGradedTransition X α F I p hact
  obtain ⟨c, hc⟩ := T.exists_image_bound
  refine ⟨c, fun n => ?_⟩
  let := moduleCohomologyModuleOfHom X α F p
  let := moduleCohomologyModuleOfHom X α (idealPower X α F I (n + c)) p
  rintro y ⟨x, rfl⟩
  have hx := hc n (idealPowerCohomologyComponentEquiv X α F I p (n + c) x)
  let e := idealPowerCohomologyZeroEquiv X α F I p
  have he := Submodule.mem_map_of_mem (f := e.toLinearMap) hx
  rw [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr e.surjective] at he
  exact (idealPowerCohomologyZeroEquiv_map X α F I p (n + c) x) ▸ he

include hact in
/-- Finite Rees cohomology over a Noetherian base kills the original inclusion kernel
under one uniform shift of the actual ideal-power transition. -/
theorem idealPowerCohomology_exists_kernel_bound [IsNoetherianRing A] :
    ∃ c : ℕ, ∀ n (x : idealPowerCohomology X α F I p (n + c)),
      moduleCohomologyMapOfHom X α (idealMultipleι X α F (I ^ (n + c))) p x = 0 →
        moduleCohomologyMapOfHom X α (idealPowerMap X α F I (Nat.le_add_right n c)) p x = 0 := by
  let := idealPowerCohomology_gradedSMul X α F I p hact
  let T := idealPowerCohomologyGradedTransition X α F I p hact
  obtain ⟨c, hc⟩ := T.exists_kernel_bound
  refine ⟨c, fun n x hx => ?_⟩
  have hz : T.map (Nat.zero_le (n + c))
      (idealPowerCohomologyComponentEquiv X α F I p (n + c) x) = 0 := by
    apply (idealPowerCohomologyZeroEquiv X α F I p).injective
    rw [_root_.map_zero]
    exact (idealPowerCohomologyZeroEquiv_map X α F I p (n + c) x).trans hx
  have hk := hc n (idealPowerCohomologyComponentEquiv X α F I p (n + c) x) hz
  change idealPowerCohomologyComponentMap X α F I p _ _ = 0 at hk
  rw [idealPowerCohomologyComponentMap_equiv] at hk
  exact (idealPowerCohomologyComponentEquiv X α F I p n).map_eq_zero_iff.mp hk

end AlgebraicGeometry.Scheme.Cohomology
