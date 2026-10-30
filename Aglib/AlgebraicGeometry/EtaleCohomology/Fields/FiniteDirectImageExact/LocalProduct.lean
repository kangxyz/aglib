/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteDirectImageExact.Sections
public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage

/-! # The original direct image is a finite product on a splitting chart -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.FiniteEtale

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields.FiniteDirectImage

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
  {V : X.Etale} {A : FintypeCat.{u}}
  (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y)

/-- The actual component inclusion, independent of the coefficient category. -/
def componentTestInclusionNatTrans (a : A) :
    siteEtalePostcompose (splitComponent Y e a) ⟶
      siteEtalePostcompose V.hom ⋙ siteBaseChange Y.obj.hom where
  app U := componentTestInclusion Y e U a
  naturality _ _ g := componentTestInclusion_naturality Y e g a

/-- Literal component restriction induced by the coefficient-free site map. -/
def splitProjection (a : A) :
    directImage Y.obj.hom ⋙ etaleRestriction V.hom ⟶
      etaleRestriction (splitComponent Y e a) := by
  letI := Functor.isContinuous_comp
    (siteEtalePostcompose (X := X) (S := V.left) V.hom)
    (siteBaseChange (X := X) (S := Y.obj.left) Y.obj.hom)
    V.left.smallEtaleTopology X.smallEtaleTopology
    Y.obj.left.smallEtaleTopology
  exact Functor.sheafPushforwardContinuousNatTrans (componentTestInclusionNatTrans Y e a)
    AddCommGrpCat.{u + 1} V.left.smallEtaleTopology Y.obj.left.smallEtaleTopology

/-- The generic continuous-site construction retains the original section map. -/
@[simp]
theorem splitProjection_app (a : A) (F : AbelianSheaf.{u, u + 1} Y.obj.left)
    (U : V.left.Etale) :
    ((splitProjection Y e a).app F).hom.app (op U) =
      F.obj.map (componentTestInclusion Y e U a).op := rfl

/-- The original local direct image, with the original component restriction maps. -/
def splitFan : Fan (fun a : A => etaleRestriction (splitComponent Y e a)) :=
  Fan.mk (directImage Y.obj.hom ⋙ etaleRestriction V.hom) (splitProjection Y e)

/-- Literal section-product bijectivity proves the functor-valued limit property. -/
def splitFanIsLimit : IsLimit (splitFan Y e) := by
  apply evaluationJointlyReflectsLimits
  intro F
  apply (Fan.isLimitMapConeEquiv
    ((CategoryTheory.evaluation _ _).obj F) _ (splitFan Y e)).symm.toFun
  apply isLimitOfReflects (sheafToPresheaf V.left.smallEtaleTopology AddCommGrpCat.{u + 1})
  apply (Fan.isLimitMapConeEquiv
    (sheafToPresheaf V.left.smallEtaleTopology AddCommGrpCat.{u + 1}) _ _).symm.toFun
  apply evaluationJointlyReflectsLimits
  intro U
  apply (Fan.isLimitMapConeEquiv ((CategoryTheory.evaluation _ _).obj U) _ _).symm.toFun
  exact AddCommGrpCat.fanIsLimitOfBijective.{u, u + 1}
    (fun a => F.obj.obj (op (componentTest Y e U.unop a)))
    (F.obj.obj (op (pullbackTest Y U.unop)))
    (fun a => F.obj.map (componentTestInclusion Y e U.unop a).op)
    (splitSections_bijective Y e F U.unop)

/-- The canonical original direct-image comparison on a labelled splitting chart. -/
def localProductIso :
    directImage Y.obj.hom ⋙ etaleRestriction V.hom ≅
      ∏ᶜ (fun a : A => etaleRestriction (splitComponent Y e a)) :=
  (splitFanIsLimit Y e).conePointUniqueUpToIso (limit.isLimit _)

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields.FiniteDirectImage
