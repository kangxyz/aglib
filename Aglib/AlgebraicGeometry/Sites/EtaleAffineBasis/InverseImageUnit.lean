/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.InverseImageLocalRepresentatives
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition

/-! # The original adjunction unit on inverse-image local representatives -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)

private lemma construction_unit :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (siteBaseChange f)
      AddCommGrpCat.{u + 1} X.smallEtaleTopology S.smallEtaleTopology).unit.app F).hom =
      (siteBaseChange f).op.lanUnit.app F.obj ≫
        Functor.whiskerLeft (siteBaseChange f).op
          (toSheafify S.smallEtaleTopology (inverseImagePresentation f F)) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    (L := Functor.sheafPullbackConstruction.sheafPullback (siteBaseChange f)
      AddCommGrpCat.{u + 1} X.smallEtaleTopology S.smallEtaleTopology)
    (R := (siteBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      X.smallEtaleTopology S.smallEtaleTopology)
    (((siteBaseChange f).op.lanAdjunction AddCommGrpCat.{u + 1}).comp
      (sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Functor.FullyFaithful.id (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (Iso.refl _) (Iso.refl _) F
  exact h.trans (by
    simp only [Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
      Iso.refl_hom, NatTrans.id_app]
    rfl)

/-- The local-presentation map sends the native Kan unit to the original
inverse-image adjunction unit, before choosing a local representative. -/
@[reassoc]
lemma inverseImagePresentationMap_unit (U : X.Etale) :
    ((siteBaseChange f).op.lanUnit.app F.obj).app (op U) ≫
        (inverseImagePresentationMap f F).app (op ((siteBaseChange f).obj U)) =
      ((inverseImageAdjunction f).unit.app F).hom.app (op U) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (siteBaseChange f)
      AddCommGrpCat.{u + 1} X.smallEtaleTopology S.smallEtaleTopology)
    (inverseImageAdjunction f) F
  have h' := congrArg
    (fun q => (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map q) h
  change ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (siteBaseChange f)
      AddCommGrpCat.{u + 1} X.smallEtaleTopology S.smallEtaleTopology).unit.app F).hom ≫
      Functor.whiskerLeft (siteBaseChange f).op
        (((Functor.sheafPullbackConstruction.sheafPullbackIso (siteBaseChange f)
          AddCommGrpCat.{u + 1} X.smallEtaleTopology S.smallEtaleTopology).inv.app F).hom) =
      ((inverseImageAdjunction f).unit.app F).hom at h'
  rw [construction_unit] at h'
  exact congrArg (fun q => q.app (op U)) h'

end AlgebraicGeometry.Scheme.EtaleAffineBasis
