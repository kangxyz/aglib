/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # The actual small-etale category of an etale chart

An object over an etale chart in the original small-etale category is itself
etale over that chart. Conversely, composition with the chart gives the inverse
functor. The underlying arrows are retained literally.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Etale

universe u

variable {X : Scheme.{u}} (U : X.Etale)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Forgetting the outer base gives the actual small-etale object over the chart. -/
def sliceForward : Over U ⥤ U.left.Etale where
  obj V := Scheme.Etale.mk V.hom.left
  map f := MorphismProperty.Over.homMk f.left.left
    (congrArg (fun g => g.left) (Over.w f))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Composing a chart with its base gives an object of the original etale slice. -/
def sliceBackward : U.left.Etale ⥤ Over U where
  obj V := Over.mk (MorphismProperty.Over.homMk V.hom (by rfl) :
    Scheme.Etale.mk (V.hom ≫ U.hom) ⟶ U)
  map {V W} f := by
    let a : Scheme.Etale.mk (V.hom ≫ U.hom) ⟶ Scheme.Etale.mk (W.hom ≫ U.hom) :=
      MorphismProperty.Over.homMk f.left (by
        change f.left ≫ (W.hom ≫ U.hom) = V.hom ≫ U.hom
        rw [← Category.assoc, MorphismProperty.Over.w f])
    exact Over.homMk a (by
      apply MorphismProperty.Over.Hom.ext
      exact MorphismProperty.Over.w f)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original etale slice is equivalent to the small-etale category of the chart. -/
def sliceEquivalence : Over U ≌ U.left.Etale where
  functor := sliceForward U
  inverse := sliceBackward U
  unitIso := NatIso.ofComponents (fun V =>
    Over.isoMk
      (MorphismProperty.Over.isoMk (Iso.refl V.left.left) (by
        change 𝟙 V.left.left ≫ (V.hom.left ≫ U.hom) = V.left.hom
        simpa only [Category.id_comp] using MorphismProperty.Over.w V.hom))
      (by apply MorphismProperty.Over.Hom.ext; exact Category.id_comp _))
    (by
      intro V W f
      ext : 1
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun V =>
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by
      change 𝟙 V.left ≫ V.hom = V.hom
      exact Category.id_comp _))
    (by intro V W f; apply MorphismProperty.Over.Hom.ext
        exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp V := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _

/-- The equivalence retains the original map of underlying schemes. -/
@[simp]
theorem sliceForward_map_left {V W : Over U} (f : V ⟶ W) :
    ((sliceForward U).map f).left = f.left.left := rfl

end AlgebraicGeometry.Scheme.Etale
