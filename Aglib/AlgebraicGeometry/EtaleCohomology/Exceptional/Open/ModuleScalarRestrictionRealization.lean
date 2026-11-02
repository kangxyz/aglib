/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestrictionImages

/-! # Original native lower-shriek scalar comparison realization cubes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)

/-- The old comparison retains its entire original realization chain. -/
theorem moduleLowerShriekScalarRestrictionIso_inv_valued (M : ModuleSheaf U Γ) :
    (moduleSheafEquivalence X Λ).inverse.map
      ((moduleLowerShriekScalarRestrictionIso j φ).inv.app M) =
    (moduleLowerShriekValuedIso j Λ).hom.app ((moduleRestrictScalars U φ).obj M) ≫
      (moduleValuedLowerShriek j Λ).map ((moduleRestrictScalarsComparison U φ).hom.app M) ≫
      (moduleValuedLowerShriekScalarRestrictionIso j φ).inv.app
        ((moduleSheafEquivalence U Γ).inverse.obj M) ≫
      (moduleValuedRestrictScalars X φ).map ((moduleLowerShriekValuedIso j Γ).inv.app M) ≫
      (moduleRestrictScalarsComparison X φ).inv.app ((moduleLowerShriek j Γ).obj M) := by
  let W := (Functor.whiskeringRight (ModuleSheaf U Γ) (ModuleSheaf X Λ)
    (ModuleValuedSheaf X Λ)).obj (moduleSheafEquivalence X Λ).inverse
  have h := congrArg (fun t => t.app M) (W.map_preimage
    (moduleLowerShriekScalarRestrictionLeftIso j φ ≪≫
      Functor.isoWhiskerLeft _ (moduleValuedLowerShriekScalarRestrictionIso j φ) ≪≫
      (moduleLowerShriekScalarRestrictionRightIso j φ).symm).inv)
  change (moduleSheafEquivalence X Λ).inverse.map
      ((moduleLowerShriekScalarRestrictionIso j φ).inv.app M) = _ at h
  simp only [moduleLowerShriekScalarRestrictionLeftIso, moduleLowerShriekScalarRestrictionRightIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] at h
  exact h.trans (Category.id_comp _)

omit [Etale j] in
/-- The old comparison retains its entire original realization chain. -/
theorem moduleInverseImageScalarRestrictionIso_hom_valued (M : ModuleSheaf X Γ) :
    (moduleSheafEquivalence U Λ).inverse.map
      ((moduleInverseImageScalarRestrictionIso j φ).hom.app M) =
    (moduleRestrictScalarsComparison U φ).hom.app ((moduleInverseImage j Γ).obj M) ≫
      (moduleValuedRestrictScalars U φ).map ((moduleInverseImageValuedIso Γ j).hom.app M) ≫
      (moduleValuedInverseImageScalarRestrictionIso j φ).hom.app
        ((moduleSheafEquivalence X Γ).inverse.obj M) ≫
      (moduleValuedInverseImage j Λ).map ((moduleRestrictScalarsComparison X φ).inv.app M) ≫
      (moduleInverseImageValuedIso Λ j).inv.app ((moduleRestrictScalars X φ).obj M) := by
  let W := (Functor.whiskeringRight (ModuleSheaf X Γ) (ModuleSheaf U Λ)
    (ModuleValuedSheaf U Λ)).obj (moduleSheafEquivalence U Λ).inverse
  have h := congrArg (fun t => t.app M) (W.map_preimage
    (moduleInverseImageScalarRestrictionLeftIso j φ ≪≫
      Functor.isoWhiskerLeft _ (moduleValuedInverseImageScalarRestrictionIso j φ) ≪≫
      (moduleInverseImageScalarRestrictionRightIso j φ).symm).hom)
  change (moduleSheafEquivalence U Λ).inverse.map
      ((moduleInverseImageScalarRestrictionIso j φ).hom.app M) = _ at h
  simp only [moduleInverseImageScalarRestrictionLeftIso,
    moduleInverseImageScalarRestrictionRightIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] at h
  exact h.trans (Category.id_comp _)

end AlgebraicGeometry.Scheme.EtaleCohomology
