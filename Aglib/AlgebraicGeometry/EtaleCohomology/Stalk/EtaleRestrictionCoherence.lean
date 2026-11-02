/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionComposition
public import Aglib.CategoryTheory.Adjunction.Mates.UnitNormalizedComposition

/-! # Native inverse-image coherence for étale chart restriction -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) [Etale f] [Etale g]

/-- The actual chart adjunction, with no reselected sheaf adjunction. -/
private abbrev etaleRestrictionAdj {Y Z : Scheme.{u}} (k : Y ⟶ Z) [Etale k] :=
  (siteEtalePostcomposeAdj k).sheafPushforwardContinuous
    (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology Y) (Scheme.smallEtaleTopology Z)

/-- The original site counit identity normalizes the whole restriction compositor. -/
private theorem etaleRestrictionComp_unit :
    let d := Functor.sheafPushforwardContinuousComp' (siteBaseChangeComp f g).symm
      AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology T)
    ((etaleRestrictionAdj f).comp (etaleRestrictionAdj g)).unit ≫
        Functor.whiskerLeft (etaleRestriction f ⋙ etaleRestriction g) d.hom =
      (etaleRestrictionAdj (g ≫ f)).unit ≫
        Functor.whiskerRight (etaleRestrictionComp f g).hom (directImage (g ≫ f)) := by
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Adjunction.comp_unit_app]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let U := V.unop
  change F.obj.map ((siteEtalePostcomposeAdj f).counit.app U).op ≫
      F.obj.map ((siteEtalePostcompose f).map
        ((siteEtalePostcomposeAdj g).counit.app ((siteBaseChange f).obj U))).op ≫
      F.obj.map ((siteEtalePostcompose f).map
        ((siteEtalePostcompose g).map ((siteBaseChangeComp f g).hom.app U))).op =
    F.obj.map ((siteEtalePostcomposeAdj (g ≫ f)).counit.app U).op ≫
      F.obj.map ((siteEtalePostcomposeComp f g).inv.app
        ((siteBaseChange (g ≫ f)).obj U)).op
  have hsite :
      (siteEtalePostcompose f).map
          ((siteEtalePostcompose g).map ((siteBaseChangeComp f g).hom.app U)) ≫
          (siteEtalePostcompose f).map
            ((siteEtalePostcomposeAdj g).counit.app ((siteBaseChange f).obj U)) ≫
          (siteEtalePostcomposeAdj f).counit.app U =
        (siteEtalePostcomposeComp f g).inv.app ((siteBaseChange (g ≫ f)).obj U) ≫
          (siteEtalePostcomposeAdj (g ≫ f)).counit.app U := by
    exact (Iso.eq_inv_comp _).mpr (siteEtalePostcomposeComp_counit f g U)
  simpa only [op_comp, Functor.map_comp, Category.assoc] using
    congrArg (fun k => F.obj.map k.op) hsite

/-- The full chosen inverse-image comparison agrees with chart restriction composition. -/
theorem inverseImageEtaleIso_comp_whole :
    (inverseImageComp f g).hom ≫
        Functor.whiskerRight (inverseImageEtaleIso f).hom (inverseImage g) ≫
        Functor.whiskerLeft (etaleRestriction f) (inverseImageEtaleIso g).hom =
      (inverseImageEtaleIso (g ≫ f)).hom ≫ (etaleRestrictionComp f g).hom := by
  let d := Functor.sheafPushforwardContinuousComp' (siteBaseChangeComp f g).symm
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology T)
  exact Adjunction.leftAdjointUniq_comp_of_unit
    (inverseImageAdjunction f) (inverseImageAdjunction g)
    (inverseImageAdjunction (g ≫ f))
    (etaleRestrictionAdj f) (etaleRestrictionAdj g) (etaleRestrictionAdj (g ≫ f))
    (inverseImageComp f g).hom d.hom (etaleRestrictionComp f g).hom
    (Adjunction.conjugateEquiv_leftAdjointCompIso_inv
      (inverseImageAdjunction f) (inverseImageAdjunction g)
      (inverseImageAdjunction (g ≫ f)) d)
    (etaleRestrictionComp_unit f g)

/-- The chosen inverse-image comparison agrees with literal chart restriction composition. -/
theorem inverseImageEtaleIso_comp (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageComp f g).hom.app F ≫
        (inverseImage g).map ((inverseImageEtaleIso f).hom.app F) ≫
        (inverseImageEtaleIso g).hom.app ((etaleRestriction f).obj F) =
      (inverseImageEtaleIso (g ≫ f)).hom.app F ≫
        (etaleRestrictionComp f g).hom.app F :=
  Adjunction.unitNormalizedComparison_comp_app (inverseImageComp f g).hom
    (inverseImageEtaleIso f).hom (inverseImageEtaleIso g).hom
    (inverseImageEtaleIso (g ≫ f)).hom (etaleRestrictionComp f g).hom
    (inverseImageEtaleIso_comp_whole f g) F

end AlgebraicGeometry.Scheme.EtaleCohomology
