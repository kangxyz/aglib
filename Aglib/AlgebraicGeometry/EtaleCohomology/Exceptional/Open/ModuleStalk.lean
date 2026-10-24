/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.Stalk

/-! # Actual module-valued geometric stalks of native extension by zero -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {X U : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The actual module-valued geometric stalk of a genuine constant-ring module sheaf. -/
def moduleGeometricStalk (η : Spec (.of Ω) ⟶ X) : ModuleSheaf X Λ ⥤ ModuleCat.{u + 1} Λ :=
  (moduleSheafEquivalence X Λ).inverse ⋙
    (pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} Λ)

/-- Forgetting the actual module stalk recovers the original abelian geometric stalk. -/
def moduleGeometricStalkUnderlyingIso (η : Spec (.of Ω) ⟶ X) :
    moduleGeometricStalk Λ η ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      SheafOfModules.toSheaf.{u + 1} (constantRing X Λ) ⋙
        (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}) := by
  let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let : PreservesColimitsOfSize.{u, u} V :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u} Λ
  let : PreservesFilteredColimitsOfSize.{u, u} V :=
    ⟨fun _ _ _ => inferInstance⟩
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((pointSmallEtale η).sheafFiberCompIso
      (A := ModuleCat.{u + 1} Λ) (B := AddCommGrpCat.{u + 1})
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafInverseUnderlyingIso X Λ) _

variable (j : U ⟶ X) [IsOpenImmersion j]

/-- The underlying native module-extension stalk is the actual abelian-extension stalk. -/
def moduleLowerShriekStalkUnderlyingIso (η : Spec (.of Ω) ⟶ X) :
    moduleLowerShriek j Λ ⋙ moduleGeometricStalk Λ η ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      SheafOfModules.toSheaf.{u + 1} (constantRing U Λ) ⋙ etaleLowerShriek j ⋙
        (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}) :=
  Functor.isoWhiskerLeft _ (moduleGeometricStalkUnderlyingIso Λ η) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleLowerShriekUnderlyingIso j Λ) _ ≪≫
    Functor.associator _ _ _

/-- Native module extension by zero has zero actual module stalk outside the open. -/
theorem isZero_moduleLowerShriek_stalk_of_no_lift
    (η : Spec (.of Ω) ⟶ X) (hη : ∀ ζ : Spec (.of Ω) ⟶ U, ζ ≫ j ≠ η)
    (M : ModuleSheaf U Λ) :
    IsZero ((moduleGeometricStalk Λ η).obj ((moduleLowerShriek j Λ).obj M)) := by
  have hz := isZero_etaleLowerShriek_stalk_of_no_lift j η hη
    ((SheafOfModules.toSheaf.{u + 1} (constantRing U Λ)).obj M)
  have h := hz.of_iso ((moduleLowerShriekStalkUnderlyingIso Λ j η).app M)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_zero_of_src _

end AlgebraicGeometry.Scheme.EtaleCohomology
