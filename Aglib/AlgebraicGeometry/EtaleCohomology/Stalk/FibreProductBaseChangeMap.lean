/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap

/-! # The original map between neighborhood fibre products

The literal scheme map and its two original projection equations are shared
by neighborhood-germ comparison and target-locality consumers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (U : S.Etale)

/-- The original map between the two neighborhood fibre-product schemes. -/
def fibreProductBaseChangeMap :
    pullback ((siteBaseChange g).obj U).hom f' ⟶ pullback U.hom f :=
  pullback.lift
    (pullback.fst ((siteBaseChange g).obj U).hom f' ≫ pullback.fst U.hom g)
    (pullback.snd ((siteBaseChange g).obj U).hom f' ≫ g') (by
      calc
        (pullback.fst ((siteBaseChange g).obj U).hom f' ≫ pullback.fst U.hom g) ≫ U.hom =
            pullback.fst ((siteBaseChange g).obj U).hom f' ≫
              (((siteBaseChange g).obj U).hom ≫ g) := by
          rw [Category.assoc, pullback.condition]
          exact congrArg (fun k : pullback U.hom g ⟶ S' =>
            pullback.fst ((siteBaseChange g).obj U).hom f' ≫ k ≫ g)
            (siteBaseChange_obj_hom g U).symm
        _ = (pullback.snd ((siteBaseChange g).obj U).hom f' ≫ f') ≫ g := by
          rw [← Category.assoc, pullback.condition]
        _ = (pullback.snd ((siteBaseChange g).obj U).hom f' ≫ g') ≫ f := by
          rw [Category.assoc, h, Category.assoc])

/-- The map retains the original projection to the source neighborhood. -/
@[reassoc]
theorem fibreProductBaseChangeMap_fst :
    fibreProductBaseChangeMap f f' g g' h U ≫ pullback.fst U.hom f =
      pullback.fst ((siteBaseChange g).obj U).hom f' ≫ pullback.fst U.hom g :=
  pullback.lift_fst _ _ _

/-- The map retains the original projection to the source scheme. -/
@[reassoc]
theorem fibreProductBaseChangeMap_snd :
    fibreProductBaseChangeMap f f' g g' h U ≫ pullback.snd U.hom f =
      pullback.snd ((siteBaseChange g).obj U).hom f' ≫ g' :=
  pullback.lift_snd _ _ _


end AlgebraicGeometry.Scheme.EtaleCohomology
