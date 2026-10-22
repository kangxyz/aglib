/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Products.IntegerBase
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
Native qcqs and finite-presentation properties of a finite-type scheme over
the actual lifted integer base. This lower supplier has no hull dependency.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u

namespace AlgebraicGeometry.Scheme
open Products

/-- The actual fixed integer base turns finite-type stages into qcqs,
finitely presented stages. -/
theorem integerFiniteType_stage_properties (X : Scheme.{u})
    [LocallyOfFiniteType (toIntegerBase X)] [QuasiCompact (toIntegerBase X)] :
    CompactSpace X ∧ QuasiSeparatedSpace X ∧
      LocallyOfFinitePresentation (toIntegerBase X) ∧ QuasiSeparated (toIntegerBase X) := by
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (toIntegerBase X)
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (toIntegerBase X),
    inferInstance, inferInstance, inferInstance⟩

/-- A finite-type scheme over the actual lifted integer base is Noetherian. -/
theorem isNoetherian_of_integerFiniteType (X : Scheme.{u})
    [LocallyOfFiniteType (toIntegerBase X)] [QuasiCompact (toIntegerBase X)] :
    IsNoetherian X := by
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (toIntegerBase X)
  have : CompactSpace X := (integerFiniteType_stage_properties X).1
  exact {}

end AlgebraicGeometry.Scheme
