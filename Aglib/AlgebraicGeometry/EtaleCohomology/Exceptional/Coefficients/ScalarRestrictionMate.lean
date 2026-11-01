/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestrictionNativeAdjunction

/-! # Actual native scalar-restriction units, counits, and mates -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

variable {X S : Scheme.{u}} (f : S ⟶ X)
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)

/-- The original native coefficient comparisons are actual adjunction mates. -/
theorem mate_moduleInverseImageScalarRestrictionIso_inv :
    (mateEquiv (moduleInverseImageAdjunction f Γ) (moduleInverseImageAdjunction f Λ)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageScalarRestrictionIso f φ).inv)).natTrans =
    (moduleDirectImageScalarRestrictionIso f φ).hom := by
  apply mateEquiv_eq_of_coefficient_cubes
    (moduleInverseImageAdjunction f Γ) (moduleInverseImageAdjunction f Λ)
    (moduleValuedInverseImageAdjunction f Γ) (moduleValuedInverseImageAdjunction f Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageValuedIso Γ f).inv)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageValuedIso Λ f).inv)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageScalarRestrictionIso f φ).inv)
    (TwoSquare.mk _ _ _ _ (moduleValuedInverseImageScalarRestrictionIso f φ).inv)
    (moduleRestrictScalarsComparison X φ).symm
    (moduleRestrictScalarsComparison S φ).inv
    (moduleDirectImageComparison f Γ).hom (moduleDirectImageComparison f Λ)
    (moduleDirectImageScalarRestrictionIso f φ).hom
    (moduleValuedDirectImageScalarRestrictionIso f φ).hom
    (mate_moduleInverseImageValuedIso_inv f Γ)
    (mate_moduleInverseImageValuedIso_inv f Λ)
    (mate_moduleValuedInverseImageScalarRestrictionIso_inv f φ)
  · intro M
    simp only [TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Iso.symm_hom]
    rw [moduleInverseImageScalarRestrictionIso_inv_valued]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    have hi := (moduleValuedInverseImage f Λ).map_id
      (((moduleSheafEquivalence X Γ).inverse ⋙ moduleValuedRestrictScalars X φ).obj M)
    exact (congrArg (fun k => k ≫
      (moduleValuedInverseImageScalarRestrictionIso f φ).inv.app
        ((moduleSheafEquivalence X Γ).inverse.obj M) ≫
      (moduleValuedRestrictScalars S φ).map ((moduleInverseImageValuedIso Γ f).inv.app M) ≫
      (moduleRestrictScalarsComparison S φ).inv.app ((moduleInverseImage f Γ).obj M)) hi).trans
        (Category.id_comp _)
  · intro M
    rw [moduleDirectImageScalarRestrictionIso_hom_valued]
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
      Iso.inv_hom_id_app]
    erw [Category.comp_id]

/-- The scalar-restriction comparison retains both original adjunction units. -/
@[reassoc]
theorem moduleInverseImageScalarRestrictionIso_unit (M : ModuleSheaf X Γ) :
    (moduleRestrictScalars X φ).map ((moduleInverseImageAdjunction f Γ).unit.app M) ≫
      (moduleDirectImageScalarRestrictionIso f φ).hom.app ((moduleInverseImage f Γ).obj M) ≫
      (moduleDirectImage f Λ).map ((moduleInverseImageScalarRestrictionIso f φ).hom.app M) =
    (moduleInverseImageAdjunction f Λ).unit.app ((moduleRestrictScalars X φ).obj M) := by
  have h := unit_mateEquiv (moduleInverseImageAdjunction f Γ)
    (moduleInverseImageAdjunction f Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageScalarRestrictionIso f φ).inv) M
  change (moduleRestrictScalars X φ).map
      ((moduleInverseImageAdjunction f Γ).unit.app M) ≫
      (mateEquiv (moduleInverseImageAdjunction f Γ) (moduleInverseImageAdjunction f Λ)
        (TwoSquare.mk _ _ _ _ (moduleInverseImageScalarRestrictionIso f φ).inv)).natTrans.app
          ((moduleInverseImage f Γ).obj M) =
    (moduleInverseImageAdjunction f Λ).unit.app ((moduleRestrictScalars X φ).obj M) ≫
      (moduleDirectImage f Λ).map
        ((moduleInverseImageScalarRestrictionIso f φ).inv.app M) at h
  rw [mate_moduleInverseImageScalarRestrictionIso_inv] at h
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  have hi := (moduleDirectImage f Λ).map_id
    ((moduleRestrictScalars X φ ⋙ moduleInverseImage f Λ).obj M)
  exact (congrArg (fun k =>
    (moduleInverseImageAdjunction f Λ).unit.app ((moduleRestrictScalars X φ).obj M) ≫ k) hi).trans
      (Category.comp_id _)

/-- The same actual mate retains the original counit; no separate comparison is chosen. -/
@[reassoc]
theorem moduleInverseImageScalarRestrictionIso_counit (M : ModuleSheaf S Γ) :
    (moduleInverseImage f Λ).map ((moduleDirectImageScalarRestrictionIso f φ).hom.app M) ≫
      (moduleInverseImageAdjunction f Λ).counit.app ((moduleRestrictScalars S φ).obj M) =
    (moduleInverseImageScalarRestrictionIso f φ).inv.app ((moduleDirectImage f Γ).obj M) ≫
      (moduleRestrictScalars S φ).map ((moduleInverseImageAdjunction f Γ).counit.app M) := by
  have h := mateEquiv_counit (moduleInverseImageAdjunction f Γ)
    (moduleInverseImageAdjunction f Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageScalarRestrictionIso f φ).inv) M
  change (moduleInverseImage f Λ).map
      ((mateEquiv (moduleInverseImageAdjunction f Γ) (moduleInverseImageAdjunction f Λ)
        (TwoSquare.mk _ _ _ _ (moduleInverseImageScalarRestrictionIso f φ).inv)).natTrans.app M) ≫
      _ = _ at h
  rw [mate_moduleInverseImageScalarRestrictionIso_inv] at h
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
