/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.Stalk

/-! # Original open counit on geometric stalks -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  {Ω : Type u} [Field Ω]

/-- A field-valued point in the open image has an actual factorization. -/
theorem exists_openImmersion_pointLift (η : Spec (.of Ω) ⟶ X)
    (hη : η (default : Spec (.of Ω)) ∈ Set.range j) :
    ∃ ζ : Spec (.of Ω) ⟶ U, ζ ≫ j = η := by
  have h : Set.range η ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    simpa only [Subsingleton.elim x (default : Spec (.of Ω))] using hη
  exact ⟨IsOpenImmersion.lift j η h, IsOpenImmersion.lift_fac j η h⟩

/-- The actual lower-shriek counit is invertible on every stalk lying in the open. -/
theorem etaleLowerShriek_counit_stalk_isIso [IsSepClosed Ω]
    (ζ : Spec (.of Ω) ⟶ U) (η : Spec (.of Ω) ⟶ X) (hζ : ζ ≫ j = η)
    (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((pointSmallEtale η).sheafFiber.map
      ((etaleLowerShriekAdjunction j).counit.app F)) := by
  subst η
  apply (NatIso.isIso_map_iff (StalkInverseImage.nativeStalkIso j ζ) _).mpr
  change IsIso ((pointSmallEtale ζ).sheafFiber.map
    ((inverseImage j).map ((etaleLowerShriekAdjunction j).counit.app F)))
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology
