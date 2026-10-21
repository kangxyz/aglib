/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.QuotientTower
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Multiplication

/-! # Original cohomology multiplication and ideal-power transitions -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) (F : X.Modules)

/-- Original coefficient scalar multiplication induces the original structural action on `H`. -/
theorem moduleCohomologyMapOfHom_globalScalar_apply (a : A) (p : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X F) p) :
    letI := moduleCohomologyModuleOfHom X α F p
    moduleCohomologyMapOfHom X α (globalScalarEndomorphism X F (α a)) p x = a • x := by
  let := moduleCohomologyModuleOfHom X α F p
  have h : (SheafOfModules.toSheaf X.ringCatSheaf).map
      (globalScalarEndomorphism X F (α a)) = moduleScalarOfGlobal X F (α a) := by
    ext U y
    exact globalScalarEndomorphism_app X F (α a) U.unop y
  change Sheaf.H.map _ p x = Sheaf.H.map _ p x
  rw [h]

/-- Lowering the action degree in original ideal-power cohomology is scalar multiplication. -/
theorem idealPowerCohomology_mul_transition (I : Ideal A) (r n p : ℕ) (a : ↥(I ^ r))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (idealPower X α F I n)) p) :
    letI := moduleCohomologyModuleOfHom X α (idealPower X α F I n) p
    moduleCohomologyMapOfHom X α (idealPowerMap X α F I (Nat.le_add_left n r)) p
      (moduleCohomologyMapOfHom X α (idealPowerMul X α F I r n a) p x) = (a : A) • x := by
  let := moduleCohomologyModuleOfHom X α (idealPower X α F I n) p
  let H := moduleCohomologyFunctorOfHom X α p
  change H.map (idealPowerMap X α F I (Nat.le_add_left n r))
    (H.map (idealPowerMul X α F I r n a) x) = _
  rw [← ModuleCat.comp_apply, ← H.map_comp, idealPowerMul_transition]
  exact moduleCohomologyMapOfHom_globalScalar_apply X α (idealPower X α F I n) a p x

end AlgebraicGeometry.Scheme.Cohomology
