/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleClosedStalk

/-! # The actual native constant-ring closed unit on original geometric stalks -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (Λ : Type (u + 1)) [Ring Λ]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- On the closed part, the original native module adjunction unit is invertible on stalks. -/
theorem moduleClosed_unit_underlying_stalk_isIso
    (ζ : Spec (.of Ω) ⟶ Z) (η : Spec (.of Ω) ⟶ X) (hζ : ζ ≫ i = η)
    (M : ModuleSheaf X Λ) :
    IsIso ((pointSmallEtale η).sheafFiber.map
      ((SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleInverseImageAdjunction i Λ).unit.app M))) := by
  apply (moduleInverseImage_unit_map_isIso_iff i Λ
    (SheafOfModules.toSheaf (constantRing X Λ) ⋙ (pointSmallEtale η).sheafFiber) M).mpr
  let e := Functor.isoWhiskerRight (moduleSheafUnderlyingIso X Λ)
    (pointSmallEtale η).sheafFiber
  have h := moduleValuedClosed_unit_underlying_stalk_isIso i Λ ζ η hζ
    ((moduleSheafEquivalence X Λ).inverse.obj M)
  exact (NatIso.isIso_map_iff e _).mpr h

end AlgebraicGeometry.Scheme.EtaleCohomology
