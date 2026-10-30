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
  pullback.map ((siteBaseChange g).obj U).hom f' U.hom f
    (pullback.fst U.hom g) g' g (by exact pullback.condition.symm) h

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
