/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SchemeLimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CounitCoefficientColimit
public import Aglib.CategoryTheory.Limits.CoconeValues
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-! # Original classes represented by original direct-image stage coefficients

Both continuity inputs are constructed from the actual affine inverse limit.
The resulting class is represented at an actual stage, and its return map is
exactly the original cohomological pullback followed by the original adjunction
counit. There is no supplied coefficient-colimit certificate, class-zero
hypothesis or higher-base-change hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u e
attribute [local instance] hasSheafifyLarge

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
  [∀ i, IsAffine (X.obj i).unop]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [HasColimitsOfShape I AddCommGrpCat.{e}]
  (F : AbelianSheaf.{u, u + 1} c.pt.unop)

/-- The original counit comparison gives the actual coefficient isomorphism
on cohomology, with no replacement of the apex coefficient. -/
def directImageLimitCohomologyIso (q : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{e}
      (colimit (coneCoefficientFunctor X c (directImageCoefficientSystem X c F))) q) ≅
        AddCommGrpCat.of (Sheaf.H.{e} F q) := by
  let : IsIso (directImageCounitComparison X c F) :=
    isIso_directImageCounitComparison X c hc F
  exact (Sheaf.functorH c.pt.unop.smallEtaleTopology q).mapIso
    (asIso (directImageCounitComparison X c F))

/-- The original stage cohomology cocone, returned to the original coefficient. -/
def directImageLimitCohomologyCocone (q : ℕ) :
    Cocone (diagramCohomologyFunctor X (directImageCoefficientSystem X c F) q) :=
  (diagramCohomologyCocone X c (directImageCoefficientSystem X c F) q).extend
    (directImageLimitCohomologyIso X c hc F q).hom

omit [HasColimitsOfShape I AddCommGrpCat.{e}] in
/-- Every leg is exactly the original pullback followed by the original counit. -/
theorem directImageLimitCohomologyCocone_leg (q : ℕ) (i : I) :
    (directImageLimitCohomologyCocone X c hc F q).ι.app i =
      cohomologyTransfer (X := (X.obj i).unop) (Y := c.pt.unop)
        (c.ι.app i).unop ((inverseImageAdjunction (c.ι.app i).unop).counit.app F) q := by
  apply ConcreteCategory.ext_apply
  intro x
  change Sheaf.H.map (directImageCounitComparison X c F) q
      (Sheaf.H.map
        (colimit.ι (coneCoefficientFunctor X c (directImageCoefficientSystem X c F)) i) q
        (cohomologyPullback (X := (X.obj i).unop) (S := c.pt.unop)
          (c.ι.app i).unop _ q x)) = _
  let z : Sheaf.H.{e}
      ((coneCoefficientFunctor X c (directImageCoefficientSystem X c F)).obj i) q :=
    cohomologyPullback (X := (X.obj i).unop) (S := c.pt.unop)
      (c.ι.app i).unop ((directImageCoefficientSystem X c F).obj i) q x
  exact (Sheaf.H.map_comp_apply
    (colimit.ι (coneCoefficientFunctor X c (directImageCoefficientSystem X c F)) i)
    (directImageCounitComparison X c F) z).symm.trans
      (congrArg (fun t => Sheaf.H.map t q z)
        (ι_directImageCounitComparison X c F i))

/-- Genuine scheme-limit continuity constructs this original counit cocone. -/
def isColimitDirectImageLimitCohomologyCocone (q : ℕ) :
    IsColimit (directImageLimitCohomologyCocone X c hc F q) := by
  exact @IsColimit.extendIso I _ AddCommGrpCat.{e} _
    (diagramCohomologyFunctor X (directImageCoefficientSystem X c F) q)
    (diagramCohomologyCocone X c (directImageCoefficientSystem X c F) q) _
    (directImageLimitCohomologyIso X c hc F q).hom
    (Iso.isIso_hom (directImageLimitCohomologyIso X c hc F q))
    (isColimitDiagramCohomologyOfQcqsStages X c hc
      (directImageCoefficientSystem X c F) q)

include hc in
/-- Every original class has an actual stage representative and the exact
original counit-transfer equation, in the original independent Ext universe. -/
theorem exists_directImage_stage_class [UnivLE.{u, e}] (q : ℕ) (a : Sheaf.H.{e} F q) :
    ∃ (i : I) (aᵢ : Sheaf.H.{e} ((directImage (c.ι.app i).unop).obj F) q),
      cohomologyTransfer (X := (X.obj i).unop) (Y := c.pt.unop)
        (c.ι.app i).unop ((inverseImageAdjunction (c.ι.app i).unop).counit.app F) q aᵢ = a := by
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{e}) :=
    preservesFilteredColimitsOfSize_of_univLE.{e, e, u, u} _
  obtain ⟨i, aᵢ, haᵢ⟩ := CoconeValues.exists_rep
    (diagramCohomologyFunctor X (directImageCoefficientSystem X c F) q)
    (isColimitDirectImageLimitCohomologyCocone X c hc F q) a
  refine ⟨i, aᵢ, ?_⟩
  rw [directImageLimitCohomologyCocone_leg] at haᵢ
  exact haᵢ

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
