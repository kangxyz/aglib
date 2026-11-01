/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleShortExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestrictionAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestrictionMate

/-! # Actual scalar restriction of the original open/closed localization sequence

All three vertices and both original arrows are compared. The first arrow is
the original lower-shriek counit, the second the original closed inverse-image
unit. Exactness of scalar restriction has no injectivity or flatness premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)

/-- The first localization vertex uses the original lower-shriek and inverse-image comparisons. -/
def moduleLocalizationScalarRestrictionFirstIso (M : ModuleSheaf X Γ) :
    (moduleRestrictScalars X φ).obj
      ((moduleLowerShriek j Γ).obj ((moduleInverseImage j Γ).obj M)) ≅
    (moduleLowerShriek j Λ).obj
      ((moduleInverseImage j Λ).obj ((moduleRestrictScalars X φ).obj M)) :=
  (moduleLowerShriekScalarRestrictionIso j φ).app ((moduleInverseImage j Γ).obj M) ≪≫
    (moduleLowerShriek j Λ).mapIso ((moduleInverseImageScalarRestrictionIso j φ).app M)

/-- The third localization vertex uses the original closed image and inverse-image comparisons. -/
def moduleLocalizationScalarRestrictionThirdIso (M : ModuleSheaf X Γ) :
    (moduleRestrictScalars X φ).obj
      ((moduleDirectImage i Γ).obj ((moduleInverseImage i Γ).obj M)) ≅
    (moduleDirectImage i Λ).obj
      ((moduleInverseImage i Λ).obj ((moduleRestrictScalars X φ).obj M)) :=
  (moduleDirectImageScalarRestrictionIso i φ).app ((moduleInverseImage i Γ).obj M) ≪≫
    (moduleDirectImage i Λ).mapIso ((moduleInverseImageScalarRestrictionIso i φ).app M)

/-- The first comparison retains the actual localization counit. -/
@[reassoc]
theorem moduleLocalizationScalarRestriction_counit (M : ModuleSheaf X Γ) :
    (moduleLocalizationScalarRestrictionFirstIso j φ M).hom ≫
      (moduleLowerShriekAdjunction j Λ).counit.app ((moduleRestrictScalars X φ).obj M) =
    (moduleRestrictScalars X φ).map ((moduleLowerShriekAdjunction j Γ).counit.app M) := by
  change ((moduleLowerShriekScalarRestrictionIso j φ).hom.app
      ((moduleInverseImage j Γ).obj M) ≫
      (moduleLowerShriek j Λ).map ((moduleInverseImageScalarRestrictionIso j φ).hom.app M)) ≫
      (moduleLowerShriekAdjunction j Λ).counit.app ((moduleRestrictScalars X φ).obj M) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (moduleLowerShriekScalarRestrictionIso j φ).hom.app
      ((moduleInverseImage j Γ).obj M) ≫ k)
        (moduleLowerShriekScalarRestrictionIso_counit j φ M)).trans
          (((moduleLowerShriekScalarRestrictionIso j φ).app
            ((moduleInverseImage j Γ).obj M)).hom_inv_id_assoc _))

omit [IsClosedImmersion i] in
/-- The third comparison retains the actual localization unit. -/
@[reassoc]
theorem moduleLocalizationScalarRestriction_unit (M : ModuleSheaf X Γ) :
    (moduleRestrictScalars X φ).map ((moduleInverseImageAdjunction i Γ).unit.app M) ≫
      (moduleLocalizationScalarRestrictionThirdIso i φ M).hom =
    (moduleInverseImageAdjunction i Λ).unit.app ((moduleRestrictScalars X φ).obj M) :=
  moduleInverseImageScalarRestrictionIso_unit i φ M

/-- Scalar restriction identifies the entire original localization short complex,
including both arrows, not merely the three objects. -/
def moduleLocalizationScalarRestrictionIso
    (hcomp : Set.range j = (Set.range i)ᶜ) (M : ModuleSheaf X Γ) :
    (moduleLocalizationShortComplex j Γ i hcomp M).map (moduleRestrictScalars X φ) ≅
      moduleLocalizationShortComplex j Λ i hcomp ((moduleRestrictScalars X φ).obj M) :=
  ShortComplex.isoMk (moduleLocalizationScalarRestrictionFirstIso j φ M)
    (Iso.refl _) (moduleLocalizationScalarRestrictionThirdIso i φ M)
    ((moduleLocalizationScalarRestriction_counit j φ M).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (moduleLocalizationScalarRestriction_unit i φ M).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
