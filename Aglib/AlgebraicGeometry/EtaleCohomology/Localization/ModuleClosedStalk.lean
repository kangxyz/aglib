/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.AdjunctionUnderlying

/-! # The original module-valued closed unit on geometric stalks -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (Λ : Type (u + 1)) [Ring Λ]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- On the closed part, the actual module-valued unit is invertible on underlying stalks. -/
theorem moduleValuedClosed_unit_underlying_stalk_isIso
    (ζ : Spec (.of Ω) ⟶ Z) (η : Spec (.of Ω) ⟶ X) (hζ : ζ ≫ i = η)
    (M : ModuleValuedSheaf X Λ) :
    IsIso ((pointSmallEtale η).sheafFiber.map
      ((sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((moduleValuedInverseImageAdjunction i Λ).unit.app M))) := by
  have h : IsIso ((pointSmallEtale η).sheafFiber.map
      ((sheafCompose (Scheme.smallEtaleTopology X)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
            ((moduleValuedInverseImageAdjunction i Λ).unit.app M) ≫
        (directImage i).map ((moduleValuedInverseImageUnderlyingIso Λ i).hom.app M))) := by
    rw [moduleValuedInverseImageUnderlyingIso_unit]
    exact closedDirectImage_unit_stalk_isIso i ζ η hζ _
  erw [CategoryTheory.Functor.map_comp] at h
  let e := (pointSmallEtale η).sheafFiber.mapIso
    ((directImage i).mapIso ((moduleValuedInverseImageUnderlyingIso Λ i).app M))
  exact (@isIso_comp_right_iff _ _ _ _ _
    ((pointSmallEtale η).sheafFiber.map
      ((sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((moduleValuedInverseImageAdjunction i Λ).unit.app M))) e.hom e.isIso_hom).mp h

end AlgebraicGeometry.Scheme.EtaleCohomology
