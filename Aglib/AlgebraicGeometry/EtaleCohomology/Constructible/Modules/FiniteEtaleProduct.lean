/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.EtaleRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteDirectImageExact.Sections
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Literal module direct-image products on finite-etale splitting charts

The component projections are the original module-valued section restrictions.
Their product property is reflected from the actual underlying abelian section
fan. Reflection of limits, rather than fullness of scalar forgetting, retains
all scalar actions and permits an independently sized commutative coefficient
ring. The splitting geometry works over an arbitrary scheme and includes the
empty fibre.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.EtaleCohomology.Fields.FiniteDirectImage

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

local instance finiteEtaleProductHasModuleLimits :
    HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, r}

variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
  {V : X.Etale} {A : FintypeCat.{u}}
  (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y)

/-- The original linear restriction to a component of the actual splitting. -/
def moduleSplitProjection (a : A) :
    moduleDirectImage R Y.obj.hom ⋙ moduleEtaleRestriction R V.hom ⟶
      moduleEtaleRestriction R (splitComponent Y e a) where
  app F := ⟨{
    app U := F.obj.map (componentTestInclusion Y e U.unop a).op
    naturality U W g := by
      change F.obj.map ((siteBaseChange Y.obj.hom).map
          ((siteEtalePostcompose V.hom).map g.unop)).op ≫
          F.obj.map (componentTestInclusion Y e W.unop a).op =
        F.obj.map (componentTestInclusion Y e U.unop a).op ≫
          F.obj.map ((siteEtalePostcompose (splitComponent Y e a)).map g.unop).op
      exact (F.obj.map_comp _ _).symm.trans
        ((congrArg (fun f => F.obj.map f.op)
          (componentTestInclusion_naturality Y e g.unop a).symm).trans
          (F.obj.map_comp _ _)) }⟩
  naturality F G h := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact (h.hom.naturality (componentTestInclusion Y e U.unop a).op).symm

/-- The native module direct image, with its literal component projections. -/
def moduleSplitFan : Fan (fun a : A => moduleEtaleRestriction R (splitComponent Y e a)) :=
  Fan.mk (moduleDirectImage R Y.obj.hom ⋙ moduleEtaleRestriction R V.hom)
    (moduleSplitProjection R Y e)

/-- The scalar-native restriction fan is limiting. Only its universal property
is reflected through forgetting scalars; no morphism is lifted by fullness. -/
def moduleSplitFanIsLimit : IsLimit (moduleSplitFan R Y e) := by
  apply evaluationJointlyReflectsLimits
  intro F
  apply (Fan.isLimitMapConeEquiv
    ((CategoryTheory.evaluation _ _).obj F) _ (moduleSplitFan R Y e)).symm.toFun
  apply isLimitOfReflects (sheafToPresheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} R))
  apply (Fan.isLimitMapConeEquiv
    (sheafToPresheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} R)) _ _).symm.toFun
  apply evaluationJointlyReflectsLimits
  intro U
  apply (Fan.isLimitMapConeEquiv ((CategoryTheory.evaluation _ _).obj U) _ _).symm.toFun
  apply isLimitOfReflects (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  apply (Fan.isLimitMapConeEquiv
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) _ _).symm.toFun
  exact AddCommGrpCat.fanIsLimitOfBijective.{u, u + 1}
    (fun a => ((moduleUnderlying R Y.obj.left).obj F).obj.obj
      (op (componentTest Y e U.unop a)))
    (((moduleUnderlying R Y.obj.left).obj F).obj.obj (op (pullbackTest Y U.unop)))
    (fun a => ((moduleUnderlying R Y.obj.left).obj F).obj.map
      (componentTestInclusion Y e U.unop a).op)
    (splitSections_bijective Y e ((moduleUnderlying R Y.obj.left).obj F) U.unop)

/-- The original functor-valued module direct-image product comparison. -/
def moduleLocalProductIso :
    moduleDirectImage R Y.obj.hom ⋙ moduleEtaleRestriction R V.hom ≅
      ∏ᶜ (fun a : A => moduleEtaleRestriction R (splitComponent Y e a)) :=
  (moduleSplitFanIsLimit R Y e).conePointUniqueUpToIso (limit.isLimit _)

/-- Its projections are the same original linear section restrictions. -/
@[reassoc (attr := simp)]
theorem moduleLocalProductIso_hom_π (a : A) :
    (moduleLocalProductIso R Y e).hom ≫
      Pi.π (fun a : A => moduleEtaleRestriction R (splitComponent Y e a)) a =
        moduleSplitProjection R Y e a :=
  (moduleSplitFanIsLimit R Y e).conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨a⟩

/-- The actual coefficient-wise product, with no replacement of the original
module direct image or its etale restriction. -/
def moduleLocalProductObjIso (F : ModuleSheaf R Y.obj.left) :
    (moduleEtaleRestriction R V.hom).obj ((moduleDirectImage R Y.obj.hom).obj F) ≅
      ∏ᶜ (fun a : A => (moduleEtaleRestriction R (splitComponent Y e a)).obj F) :=
  (moduleLocalProductIso R Y e).app F ≪≫
    PreservesProduct.iso ((CategoryTheory.evaluation _ _).obj F)
      (fun a : A => moduleEtaleRestriction R (splitComponent Y e a))

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
