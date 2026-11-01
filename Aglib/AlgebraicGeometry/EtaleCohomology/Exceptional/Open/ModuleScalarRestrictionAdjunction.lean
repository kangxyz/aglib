/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestrictionRealization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleLowerShriekValuedAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestrictionValuedAdjunction
public import Aglib.CategoryTheory.Adjunction.CoefficientMateDescent

/-! # The original genuine lower-shriek scalar comparison retains its adjunction maps -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)

/-- The old native lower-shriek scalar comparison has the original native pullback
scalar comparison as its actual adjunction mate. -/
theorem mate_moduleLowerShriekScalarRestrictionIso_inv :
    (mateEquiv (moduleLowerShriekAdjunction j Γ) (moduleLowerShriekAdjunction j Λ)
      (TwoSquare.mk _ _ _ _ (moduleLowerShriekScalarRestrictionIso j φ).inv)).natTrans =
    (moduleInverseImageScalarRestrictionIso j φ).hom := by
  apply mateEquiv_eq_of_coefficient_cubes
    (moduleLowerShriekAdjunction j Γ) (moduleLowerShriekAdjunction j Λ)
    (moduleValuedLowerShriekAdjunction j Γ) (moduleValuedLowerShriekAdjunction j Λ)
    (TwoSquare.mk _ _ _ _ (moduleLowerShriekValuedIso j Γ).inv)
    (TwoSquare.mk _ _ _ _ (moduleLowerShriekValuedIso j Λ).inv)
    (TwoSquare.mk _ _ _ _ (moduleLowerShriekScalarRestrictionIso j φ).inv)
    (TwoSquare.mk _ _ _ _ (moduleValuedLowerShriekScalarRestrictionIso j φ).inv)
    (moduleRestrictScalarsComparison U φ).symm
    (moduleRestrictScalarsComparison X φ).inv
    (moduleInverseImageValuedIso Γ j).hom (moduleInverseImageValuedIso Λ j)
    (moduleInverseImageScalarRestrictionIso j φ).hom
    (moduleValuedInverseImageScalarRestrictionIso j φ).hom
    (mate_moduleLowerShriekValuedIso_inv j Γ)
    (mate_moduleLowerShriekValuedIso_inv j Λ)
    (mate_moduleValuedLowerShriekScalarRestrictionIso_inv j φ)
  · intro M
    simp only [TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Iso.symm_hom]
    rw [moduleLowerShriekScalarRestrictionIso_inv_valued]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    have hi := (moduleValuedLowerShriek j Λ).map_id
      (((moduleSheafEquivalence U Γ).inverse ⋙ moduleValuedRestrictScalars U φ).obj M)
    exact (congrArg (fun k => k ≫
      (moduleValuedLowerShriekScalarRestrictionIso j φ).inv.app
        ((moduleSheafEquivalence U Γ).inverse.obj M) ≫
      (moduleValuedRestrictScalars X φ).map ((moduleLowerShriekValuedIso j Γ).inv.app M) ≫
      (moduleRestrictScalarsComparison X φ).inv.app ((moduleLowerShriek j Γ).obj M)) hi).trans
        (Category.id_comp _)
  · intro M
    rw [moduleInverseImageScalarRestrictionIso_hom_valued]
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]

/-- The same original mate retains the native lower-shriek unit. -/
@[reassoc]
theorem moduleLowerShriekScalarRestrictionIso_unit (M : ModuleSheaf U Γ) :
    (moduleRestrictScalars U φ).map ((moduleLowerShriekAdjunction j Γ).unit.app M) ≫
      (moduleInverseImageScalarRestrictionIso j φ).hom.app ((moduleLowerShriek j Γ).obj M) ≫
      (moduleInverseImage j Λ).map ((moduleLowerShriekScalarRestrictionIso j φ).hom.app M) =
    (moduleLowerShriekAdjunction j Λ).unit.app ((moduleRestrictScalars U φ).obj M) := by
  have h := unit_mateEquiv (moduleLowerShriekAdjunction j Γ)
    (moduleLowerShriekAdjunction j Λ)
    (TwoSquare.mk _ _ _ _ (moduleLowerShriekScalarRestrictionIso j φ).inv) M
  change (moduleRestrictScalars U φ).map ((moduleLowerShriekAdjunction j Γ).unit.app M) ≫
      (mateEquiv (moduleLowerShriekAdjunction j Γ) (moduleLowerShriekAdjunction j Λ)
        (TwoSquare.mk _ _ _ _ (moduleLowerShriekScalarRestrictionIso j φ).inv)).natTrans.app
          ((moduleLowerShriek j Γ).obj M) =
    (moduleLowerShriekAdjunction j Λ).unit.app ((moduleRestrictScalars U φ).obj M) ≫
      (moduleInverseImage j Λ).map ((moduleLowerShriekScalarRestrictionIso j φ).inv.app M) at h
  rw [mate_moduleLowerShriekScalarRestrictionIso_inv] at h
  have hc := congrArg (fun k => k ≫ (moduleInverseImage j Λ).map
    ((moduleLowerShriekScalarRestrictionIso j φ).hom.app M)) h
  have hi := ((moduleInverseImage j Λ).mapIso
    ((moduleLowerShriekScalarRestrictionIso j φ).app M)).inv_hom_id
  exact (Category.assoc _ _ _).symm.trans (hc.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun k => (moduleLowerShriekAdjunction j Λ).unit.app
      ((moduleRestrictScalars U φ).obj M) ≫ k) hi).trans (Category.comp_id _))))

/-- The same original mate retains the lower-shriek counit used by localization. -/
@[reassoc]
theorem moduleLowerShriekScalarRestrictionIso_counit (M : ModuleSheaf X Γ) :
    (moduleLowerShriek j Λ).map ((moduleInverseImageScalarRestrictionIso j φ).hom.app M) ≫
      (moduleLowerShriekAdjunction j Λ).counit.app ((moduleRestrictScalars X φ).obj M) =
    (moduleLowerShriekScalarRestrictionIso j φ).inv.app ((moduleInverseImage j Γ).obj M) ≫
      (moduleRestrictScalars X φ).map ((moduleLowerShriekAdjunction j Γ).counit.app M) := by
  have h := mateEquiv_counit (moduleLowerShriekAdjunction j Γ)
    (moduleLowerShriekAdjunction j Λ)
    (TwoSquare.mk _ _ _ _ (moduleLowerShriekScalarRestrictionIso j φ).inv) M
  change (moduleLowerShriek j Λ).map
      ((mateEquiv (moduleLowerShriekAdjunction j Γ) (moduleLowerShriekAdjunction j Λ)
        (TwoSquare.mk _ _ _ _ (moduleLowerShriekScalarRestrictionIso j φ).inv)).natTrans.app M) ≫
      _ = _ at h
  rw [mate_moduleLowerShriekScalarRestrictionIso_inv] at h
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology
