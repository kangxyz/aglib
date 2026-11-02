/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffinePresheaf
public import Aglib.CategoryTheory.Sites.Continuous.SheafificationComparison

/-! # Comparison with the original étale higher direct image

The proved affine-test presheaf isomorphism is sheafified through the native
continuous/cocontinuous restriction comparison. Full faithfulness of the actual
affine restriction returns an isomorphism of the unchanged sheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry.Scheme.Cohomology

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s}
    (Sheaf ((smallEtaleTopology X).over ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback U.hom f))]

local instance :
    (((Scheme.Modules.pushforward f).rightDerived q).obj M).IsQuasicoherent :=
  moduleHigherDirectImage_isQuasicoherent f M q

local instance (U : S.AffineEtale) : Etale ((Scheme.AffineEtale.Spec S).obj U).hom :=
  ((Scheme.AffineEtale.Spec S).obj U).prop

local instance (U : S.AffineEtale) :
    Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) (additiveCoefficient X M) q
      ((siteBaseChange f).obj ((Scheme.AffineEtale.Spec S).obj U))) :=
  originalCohomologyPresheaf_small f (additiveCoefficient X M) q
    (op ((Scheme.AffineEtale.Spec S).obj U))

/-- The assembled affine component is the single original four-edge value equivalence. -/
theorem higherDirectImageAffinePresheafIso_hom_app (U : S.AffineEtale) :
    (higherDirectImageAffinePresheafIso.{u, w, s, e} f M q).hom.app (op U) =
      AddCommGrpCat.ofHom
        (higherDirectImageAffineValueEquiv.{u, w, s, e} f M q U).toAddMonoidHom := rfl

/-- The actual affine restriction comparison, using original sheafification and
its native compatibility with restriction. -/
def higherDirectImageAffineRestrictionIso :
    (EtaleAffineBasis.abelianRestriction S).obj
      (additiveCoefficient S (((Scheme.Modules.pushforward f).rightDerived q).obj M)) ≅
    (EtaleAffineBasis.abelianRestriction S).obj
      ((higherDirectImage f q).obj (additiveCoefficient X M)) :=
  (Scheme.AffineEtale.Spec S).restrictedSheafificationComparison AddCommGrpCat.{u + 1}
    (Scheme.AffineEtale.topology S) (smallEtaleTopology S)
    ((EtaleAffineBasis.abelianRestriction S).obj
      (additiveCoefficient S (((Scheme.Modules.pushforward f).rightDerived q).obj M)))
    (smallOriginalCohomologyPresheaf f (additiveCoefficient X M) q)
    ((higherDirectImage f q).obj (additiveCoefficient X M))
    (higherDirectImageAffinePresheafIso.{u, w, s, e} f M q)
    (originalCohomologySheafificationIso f (additiveCoefficient X M) q)

/-- On the actual affine subsite, the forward arrow is the proved presheaf
comparison followed by the original higher-image sheafification unit. -/
theorem higherDirectImageAffineRestrictionIso_unit :
    (higherDirectImageAffineRestrictionIso.{u, w, s, e} f M q).hom.hom =
      (higherDirectImageAffinePresheafIso.{u, w, s, e} f M q).hom ≫
        Functor.whiskerLeft (Scheme.AffineEtale.Spec S).op
          (originalCohomologyToHigherDirectImage f (additiveCoefficient X M) q) := by
  have h := (Scheme.AffineEtale.Spec S).restrictedSheafificationComparison_hom
    AddCommGrpCat.{u + 1} (Scheme.AffineEtale.topology S) (smallEtaleTopology S)
    ((EtaleAffineBasis.abelianRestriction S).obj
      (additiveCoefficient S (((Scheme.Modules.pushforward f).rightDerived q).obj M)))
    (smallOriginalCohomologyPresheaf f (additiveCoefficient X M) q)
    ((higherDirectImage f q).obj (additiveCoefficient X M))
    (higherDirectImageAffinePresheafIso.{u, w, s, e} f M q)
    (originalCohomologySheafificationIso f (additiveCoefficient X M) q)
  exact h.trans (congrArg (fun η =>
    (higherDirectImageAffinePresheafIso.{u, w, s, e} f M q).hom ≫
      Functor.whiskerLeft (Scheme.AffineEtale.Spec S).op η)
    (originalCohomologyToHigherDirectImage_unit f (additiveCoefficient X M) q))

/-- The relative comparison between the actual native module higher image and
the original étale higher direct image. No properness or Noetherian premise is
required; these belong only to subsequent finiteness theorems. -/
def higherDirectImageComparison :
    additiveCoefficient S (((Scheme.Modules.pushforward f).rightDerived q).obj M) ≅
      (higherDirectImage f q).obj (additiveCoefficient X M) :=
  (EtaleAffineBasis.abelianRestriction S).preimageIso
    (higherDirectImageAffineRestrictionIso.{u, w, s, e} f M q)

/-- The global comparison has exactly the original assembled affine restriction. -/
theorem higherDirectImageComparison_restrict :
    (EtaleAffineBasis.abelianRestriction S).mapIso
      (higherDirectImageComparison.{u, w, s, e} f M q) =
    higherDirectImageAffineRestrictionIso.{u, w, s, e} f M q := by
  apply Iso.ext
  exact Functor.map_preimage (EtaleAffineBasis.abelianRestriction S)
    (higherDirectImageAffineRestrictionIso.{u, w, s, e} f M q).hom

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
