/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction

/-! # The actual category of the small étale slice -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {X : Scheme.{u}} (U : X.Etale)

/-- An étale object over the chart is an object of the chart's own small étale site. -/
def etaleSliceForward : Over U ⥤ U.left.Etale where
  obj V := Scheme.Etale.mk V.hom.left
  map g := MorphismProperty.Over.homMk g.left.left (by
    exact congrArg (fun k => k.left) (Over.w g))

/-- An étale object on the chart is regarded over the original base by composition. -/
def etaleSliceBackward : U.left.Etale ⥤ Over U where
  obj V := Over.mk
    (MorphismProperty.Over.homMk V.hom :
      (siteEtalePostcompose U.hom).obj V ⟶ U)
  map g := Over.homMk ((siteEtalePostcompose U.hom).map g) (by
    apply MorphismProperty.Over.Hom.ext
    exact MorphismProperty.Over.w g)

/-- The genuine slice-category equivalence retains the original underlying schemes. -/
def etaleSliceEquivalence : Over U ≌ U.left.Etale where
  functor := etaleSliceForward U
  inverse := etaleSliceBackward U
  unitIso := NatIso.ofComponents
    (fun V => Over.isoMk
      (MorphismProperty.Over.isoMk (Iso.refl _) (by
        change 𝟙 V.left.left ≫ (V.hom.left ≫ U.hom) = V.left.hom
        exact (Category.id_comp _).trans (MorphismProperty.Over.w V.hom))) (by
        apply MorphismProperty.Over.Hom.ext
        change 𝟙 V.left.left ≫ V.hom.left = V.hom.left
        exact Category.id_comp _))
    (fun g => by
      apply Over.OverMorphism.ext
      apply MorphismProperty.Over.Hom.ext
      change g.left.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left.left
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents
    (fun V => MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _))
    (fun g => by
      apply MorphismProperty.Over.Hom.ext
      change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Returning to the original small étale site is literal chart postcomposition. -/
theorem etaleSliceBackward_forget :
    etaleSliceBackward U ⋙ Over.forget U = siteEtalePostcompose U.hom := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
