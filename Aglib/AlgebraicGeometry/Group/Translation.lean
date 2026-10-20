/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Translation by an actual section of a group scheme

Translation acts by the literal point multiplication on every test
scheme. Evaluation at the unit makes its monoid representation injective.
No field, finiteness, properness or connectedness hypothesis is needed.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.Kernel.DeckTranslation`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`33acd4de918213b1df6ea400e2e24fe427c09a62920a493b838706a77be2a337`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.Translation

universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} {G : Grp (Over S)}

/-- Actual translation by a rational point, as an endomorphism of the scheme. -/
def translation (a : 𝟙_ (Over S) ⟶ G.X) : End G.X :=
  (toUnit G.X ≫ a) * 𝟙 G.X

/-- Translation on every test scheme is literal multiplication of points. -/
@[simp] theorem comp_translation {T : Over S} (x : T ⟶ G.X)
    (a : 𝟙_ (Over S) ⟶ G.X) :
    x ≫ translation a = (toUnit T ≫ a) * x := by
  simp [translation, MonObj.comp_mul]

/-- Evaluation at the actual origin recovers the translating point. -/
@[simp] theorem origin_translation (a : 𝟙_ (Over S) ⟶ G.X) :
    η[G.X] ≫ translation a = a := by
  simp only [comp_translation, toUnit_unit, Category.id_comp]
  rw [MonObj.one_eq_one]
  exact mul_one a

/-- Translation is an injective monoid representation on the actual scheme. -/
def translationHom : (𝟙_ (Over S) ⟶ G.X) →* End G.X where
  toFun := translation
  map_one' := by simp [translation]
  map_mul' a b := by
    change (toUnit G.X ≫ (a * b)) * 𝟙 G.X = translation b ≫ translation a
    simp only [translation, MonObj.comp_mul]
    simp [_root_.mul_assoc]

theorem translationHom_injective : Function.Injective (translationHom (G := G)) := by
  intro a b h
  have := congrArg (fun f => η[G.X] ≫ f) h
  simpa only [translationHom, MonoidHom.coe_mk, OneHom.coe_mk, origin_translation] using this

end AlgebraicGeometry.Scheme.Group.Translation
