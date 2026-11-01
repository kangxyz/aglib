/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Monoidal.Grp.TranslationFamily
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Translation

/-!
# The original Picard translation family through the canonical shear

The existing Picard translation morphism is exactly the first projection
after the same generic translation-family isomorphism. The original parameter
map, unit axis, translated class, actual bundle class and normalized class
retain this correspondence on every test scheme. No new family realization,
curve hypothesis, properness or smoothness is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

open Modules.Invertible

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

/-- The existing translation morphism is the first projection after the
same whole translation-family isomorphism. -/
theorem translationFamilyMorphism_eq_translationFamily_hom_fst
    {T : Over (Spec (.of k))} (t : T ⟶ G) :
    translationFamilyMorphism G t = (GrpObj.translationFamily G t).hom ≫ fst G T :=
  (GrpObj.translationFamily_hom_fst G t).symm

omit [GrpObj G] in
/-- The original Picard parameter map is the native cartesian tensor map. -/
theorem translationFamilyMap_eq_tensorHom {T T' : Over (Spec (.of k))} (f : T' ⟶ T) :
    translationFamilyMap G f = 𝟙 G ⊗ₘ f := by
  ext1 <;> simp [translationFamilyMap]

/-- Naturality of the whole shear uses exactly the existing Picard family
parameter map, not a separately chosen map of products. -/
@[reassoc]
theorem translationFamily_hom_naturality {T T' : Over (Spec (.of k))}
    (f : T' ⟶ T) (t : T ⟶ G) :
    translationFamilyMap G f ≫ (GrpObj.translationFamily G t).hom =
      (GrpObj.translationFamily G (f ≫ t)).hom ≫ translationFamilyMap G f := by
  rw [translationFamilyMap_eq_tensorHom]
  exact GrpObj.translationFamily_naturality G f t

/-- The same isomorphism sends the original unit axis to the parameter
graph as a whole morphism of schemes over the field. -/
theorem unit_axis_comp_translationFamily_hom {T : Over (Spec (.of k))} (t : T ⟶ G) :
    lift (1 : T ⟶ G) (𝟙 T) ≫ (GrpObj.translationFamily G t).hom = lift t (𝟙 T) := by
  ext1 <;> simp [MonObj.comp_mul]

-- Retain the native over-product and scheme-pullback presentations of the family.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original translated Picard class is pullback by the canonical
translation isomorphism minus the original class pulled from G. -/
theorem translationFamilyClass_eq_translationFamily_pullback
    {T : Over (Spec (.of k))} (t : T ⟶ G) (a : PicardGroup G.left) :
    translationFamilyClass G t a =
      pullbackClass (GrpObj.translationFamily G t).hom.left
        (pullbackClass (fst G T).left a) - pullbackClass (fst G T).left a := by
  rw [translationFamilyClass, translationFamilyMorphism_eq_translationFamily_hom_fst,
    Over.comp_left, pullbackClass_comp]

/-- The existing actual line-bundle constructor has the same canonical
shear pullback class; no new line-bundle constructor is introduced. -/
theorem classOf_translationFamilyLineBundle_eq_translationFamily_pullback
    {T : Over (Spec (.of k))} (t : T ⟶ G) (L : LineBundle G.left) :
    classOf _ (translationFamilyLineBundle G t L) =
      pullbackClass (GrpObj.translationFamily G t).hom.left
        (pullbackClass (fst G T).left (classOf _ L)) -
          pullbackClass (fst G T).left (classOf _ L) := by
  rw [classOf_translationFamilyLineBundle, translationFamilyClass_eq_translationFamily_pullback]

-- Identify the same native over-product with its literal family pullback.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Normalization retains the original unit-axis correction after the
translation isomorphism is made explicit. -/
theorem normalized_translationFamilyClass_eq_translationFamily_pullback
    {T : Over (Spec (.of k))} (t : T ⟶ G) (a : PicardGroup G.left) :
    (normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
      (translationFamilyClass G t a)).val =
        pullbackClass (GrpObj.translationFamily G t).hom.left
          (pullbackClass (fst G T).left a) - pullbackClass (fst G T).left a -
            pullbackClass (snd G T).left (pullbackClass t.left a) := by
  rw [normalized_translationFamilyClass_val, translationFamilyClass_eq_translationFamily_pullback]
  rfl

end AlgebraicGeometry.Scheme.RelativePicard
