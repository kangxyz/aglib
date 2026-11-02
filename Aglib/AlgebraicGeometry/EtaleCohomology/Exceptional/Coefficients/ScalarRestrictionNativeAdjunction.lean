/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestrictionAdjunction
public import Aglib.CategoryTheory.Adjunction.CoefficientMateDescent
public import Aglib.CategoryTheory.Adjunction.UnderlyingMate

/-! # Genuine coefficient-restriction adjunction compatibility -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

variable {X S : Scheme.{u}} (f : S ⟶ X)
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)

/-- The native-to-valued comparisons are the actual adjunction mates. -/
theorem mate_moduleInverseImageValuedIso_inv (R : Type (u + 1)) [Ring R] :
    (mateEquiv (moduleInverseImageAdjunction f R) (moduleValuedInverseImageAdjunction f R)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageValuedIso R f).inv)).natTrans =
    (moduleDirectImageComparison f R).hom :=
  mateEquiv_inv_natTrans_eq_of_unit _ _ _ _ (moduleInverseImageValuedIso_unit f R)

/-- The native coefficient comparison retains its complete original realization chain. -/
theorem moduleDirectImageScalarRestrictionIso_hom_valued (M : ModuleSheaf S Γ) :
    (moduleSheafEquivalence X Λ).inverse.map
      ((moduleDirectImageScalarRestrictionIso f φ).hom.app M) =
    (moduleRestrictScalarsComparison X φ).hom.app ((moduleDirectImage f Γ).obj M) ≫
      (moduleValuedRestrictScalars X φ).map ((moduleDirectImageComparison f Γ).hom.app M) ≫
      (moduleValuedDirectImageScalarRestrictionIso f φ).hom.app
        ((moduleSheafEquivalence S Γ).inverse.obj M) ≫
      (moduleValuedDirectImage f Λ).map ((moduleRestrictScalarsComparison S φ).inv.app M) ≫
      (moduleDirectImageComparison f Λ).inv.app ((moduleRestrictScalars S φ).obj M) := by
  let W := (Functor.whiskeringRight (ModuleSheaf S Γ) (ModuleSheaf X Λ)
    (ModuleValuedSheaf X Λ)).obj (moduleSheafEquivalence X Λ).inverse
  have h := congrArg (fun t => t.app M) (W.map_preimage
    (moduleDirectImageScalarRestrictionLeftIso f φ ≪≫
      Functor.isoWhiskerLeft _ (moduleValuedDirectImageScalarRestrictionIso f φ) ≪≫
      (moduleDirectImageScalarRestrictionRightIso f φ).symm).hom)
  change (moduleSheafEquivalence X Λ).inverse.map
      ((moduleDirectImageScalarRestrictionIso f φ).hom.app M) = _ at h
  simp only [moduleDirectImageScalarRestrictionLeftIso,
    moduleDirectImageScalarRestrictionRightIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] at h
  exact h.trans (Category.id_comp _)

/-- The native coefficient comparison retains its complete original realization chain. -/
theorem moduleInverseImageScalarRestrictionIso_inv_valued (M : ModuleSheaf X Γ) :
    (moduleSheafEquivalence S Λ).inverse.map
      ((moduleInverseImageScalarRestrictionIso f φ).inv.app M) =
    (moduleInverseImageValuedIso Λ f).hom.app ((moduleRestrictScalars X φ).obj M) ≫
      (moduleValuedInverseImage f Λ).map ((moduleRestrictScalarsComparison X φ).hom.app M) ≫
      (moduleValuedInverseImageScalarRestrictionIso f φ).inv.app
        ((moduleSheafEquivalence X Γ).inverse.obj M) ≫
      (moduleValuedRestrictScalars S φ).map ((moduleInverseImageValuedIso Γ f).inv.app M) ≫
      (moduleRestrictScalarsComparison S φ).inv.app ((moduleInverseImage f Γ).obj M) := by
  let W := (Functor.whiskeringRight (ModuleSheaf X Γ) (ModuleSheaf S Λ)
    (ModuleValuedSheaf S Λ)).obj (moduleSheafEquivalence S Λ).inverse
  have h := congrArg (fun t => t.app M) (W.map_preimage
    (moduleInverseImageScalarRestrictionLeftIso f φ ≪≫
      Functor.isoWhiskerLeft _ (moduleValuedInverseImageScalarRestrictionIso f φ) ≪≫
      (moduleInverseImageScalarRestrictionRightIso f φ).symm).inv)
  change (moduleSheafEquivalence S Λ).inverse.map
      ((moduleInverseImageScalarRestrictionIso f φ).inv.app M) = _ at h
  simp only [moduleInverseImageScalarRestrictionLeftIso,
    moduleInverseImageScalarRestrictionRightIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] at h
  exact h.trans (Category.id_comp _)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
