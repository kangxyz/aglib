/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIsomorphism

/-! # The original canonical unbounded comparison along a scheme isomorphism -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU wX
variable (Λ : Type (u + 1)) [Ring Λ] {U X : Scheme.{u}}
  (j : U ⟶ X) [IsIso j]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The actual lower-shriek counit is invertible on every original complex localization. -/
theorem moduleUnboundedDerivedLowerShriek_counit_Q_isIso
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    IsIso ((moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit.app
      (DerivedCategory.Q.obj K)) := by
  let : (moduleInverseImage j Λ).IsEquivalence :=
    (moduleInverseImageEquivalence Λ (asIso j)).isEquivalence_functor
  have hc : IsIso
      (((moduleLowerShriekAdjunction j Λ).mapHomologicalComplex (.up ℤ)).counit.app K) := by
    have hf (n : ℤ) : IsIso
        ((((moduleLowerShriekAdjunction j Λ).mapHomologicalComplex (.up ℤ)).counit.app K).f n) := by
      change IsIso ((moduleLowerShriekAdjunction j Λ).counit.app (K.X n))
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  rw [moduleUnboundedDerivedLowerShriekAdjunction_counit_app]
  infer_instance

/-- All-complex localization, not bounded-below restriction, detects this invertible counit. -/
theorem moduleUnboundedDerivedLowerShriek_counit_isIso_of_isIso :
    IsIso (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit := by
  let Q := DerivedCategory.Q (C := ModuleSheaf X Λ)
  let : Q.EssSurj := Localization.essSurj Q (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
  have h (K : DerivedCategory (ModuleSheaf X Λ)) :
      IsIso ((moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit.app K) := by
    rw [← NatTrans.isIso_app_iff_of_iso _ (Q.objObjPreimageIso K)]
    exact moduleUnboundedDerivedLowerShriek_counit_Q_isIso Λ j (Q.objPreimage K)
  exact NatIso.isIso_of_isIso_app _

/-- The same original canonical outer-adjoint map is an iso along a scheme isomorphism. -/
theorem moduleUnboundedLowerShriekToDirectImage_isIso_of_isIso :
    IsIso (moduleUnboundedLowerShriekToDirectImage Λ j) := by
  let := moduleUnboundedDerivedLowerShriek_counit_isIso_of_isIso Λ j
  let h := (moduleUnboundedDerivedLowerShriekAdjunction j Λ).fullyFaithfulROfIsIsoCounit
  let := h.full
  let := h.faithful
  have hi (K : DerivedCategory (ModuleSheaf U Λ)) :
      IsIso ((moduleUnboundedLowerShriekToDirectImage Λ j).app K) := by
    rw [Adjunction.Triple.leftToRight_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _
end AlgebraicGeometry.Scheme.EtaleCohomology
