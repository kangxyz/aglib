/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestrictionImages
public import Aglib.CategoryTheory.Adjunction.UnderlyingMate

/-! # Original coefficient-restriction adjunction equations -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyModules moduleRestrictScalars_preservesSheafification

variable {X S : Scheme.{u}} (f : S ⟶ X)
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)

/-- The specified module-valued coefficient comparison preserves the original unit. -/
@[reassoc]
theorem moduleValuedInverseImageScalarRestrictionIso_unit (M : ModuleValuedSheaf X Γ) :
    (moduleValuedRestrictScalars X φ).map
        ((moduleValuedInverseImageAdjunction f Γ).unit.app M) ≫
      (moduleValuedDirectImage f Λ).map
        ((moduleValuedInverseImageScalarRestrictionIso f φ).hom.app M) =
    (moduleValuedInverseImageAdjunction f Λ).unit.app
      ((moduleValuedRestrictScalars X φ).obj M) := by
  let : (ModuleCat.restrictScalars.{u + 1} φ).PreservesLeftKanExtensions
      (siteBaseChange f).op := by
    intro P
    infer_instance
  have h := Functor.sheafPullbackCoefficientIso_unit (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (ModuleCat.restrictScalars.{u + 1} φ) M
  change (moduleValuedInverseImageAdjunction f Λ).unit.app
      ((moduleValuedRestrictScalars X φ).obj M) ≫
      (moduleValuedDirectImage f Λ).map
        ((moduleValuedInverseImageScalarRestrictionIso f φ).inv.app M) =
    (moduleValuedRestrictScalars X φ).map
      ((moduleValuedInverseImageAdjunction f Γ).unit.app M) at h
  rw [← h]
  erw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The two specified module-valued comparisons are actual adjunction mates. -/
theorem mate_moduleValuedInverseImageScalarRestrictionIso_inv :
    (mateEquiv (moduleValuedInverseImageAdjunction f Γ)
      (moduleValuedInverseImageAdjunction f Λ)
      (TwoSquare.mk _ _ _ _ (moduleValuedInverseImageScalarRestrictionIso f φ).inv)).natTrans =
    (moduleValuedDirectImageScalarRestrictionIso f φ).hom := by
  apply mateEquiv_inv_natTrans_eq_of_unit
  intro M
  change (moduleValuedRestrictScalars X φ).map
      ((moduleValuedInverseImageAdjunction f Γ).unit.app M) ≫ 𝟙 _ ≫
      (moduleValuedDirectImage f Λ).map
        ((moduleValuedInverseImageScalarRestrictionIso f φ).hom.app M) = _
  erw [Category.id_comp]
  exact moduleValuedInverseImageScalarRestrictionIso_unit f φ M

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
