/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationTower
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.KilledSubobject

/-! # Original nilpotent ideal actions on ordinary relation modules -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}
  {P F : AdicSystem X K} (φ : P ⟶ F)

/-- Ordinary relation kernels retain the actual finite-stage annihilation. -/
theorem relation_killed (n : ℕ) : killedByIdealSheaf (K ^ n) (relation φ n) :=
  killedByIdealSheaf_of_mono (K ^ n) (kernel.ι (φ.hom.app (op n)))
    (P.property.annihilated n)

/-- The original affine ideal acts nilpotently on the actual relation sections,
without a cartesian condition on the relation tower. -/
theorem relation_pow_smul_top_eq_bot (n : ℕ) (U : X.affineOpens) :
    (K.ideal U) ^ n • (⊤ : Submodule Γ(X, U.1) Γ(relation φ n, U.1)) = ⊥ := by
  apply le_bot_iff.mp
  apply Submodule.smul_le.mpr
  intro a ha x _
  exact relation_killed φ n U a ha x

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
