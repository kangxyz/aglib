/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionLeftUnitTransport
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekCoherence

/-! # Original lower-shriek identity normalization in the left-unit triangle -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ))

omit [QuasiCompact f] in
/-- The actual unit-tower expansion is normalized by the original lower-shriek identity. -/
theorem moduleUnboundedLeftUnitTargetExpansion_identity :
    moduleUnboundedLeftUnitTargetExpansion C Λ hX hD ≪≫
      Functor.isoWhiskerRight (@moduleUnboundedDerivedLowerShriekIdIso Λ _ X hX)
        (@moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) ≪≫
      Functor.leftUnitor (@moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) =
      Iso.refl (@moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) := by
  unfold moduleUnboundedLeftUnitTargetExpansion
  simp only [Iso.trans_assoc]
  rw [@moduleUnboundedDerivedLowerShriekCompIso_comp_id Λ _ C.Xbar X C.j _ hD hX]
  simp only [eqToIso_trans, eqToIso_refl]

end AlgebraicGeometry.Scheme.EtaleCohomology
