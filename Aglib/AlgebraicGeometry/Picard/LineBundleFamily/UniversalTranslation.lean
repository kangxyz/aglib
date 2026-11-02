/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Translation

/-!
# Translation of an arbitrary line-bundle family

For the original family on `G × D`, simultaneous maps `t : T ⟶ G` and
`d : T ⟶ D` give the actual family `(x,s) ↦ (x * t(s), d(s))`. Its
difference from the unshifted pullback, its normalization, and all parameter
pullbacks use the existing Picard classes and line bundles. Test schemes
are arbitrary, including nonreduced schemes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  {D T T' : Over (Spec (.of k))}

/-- The original translated map into an arbitrary family. -/
def universalTranslationMorphism (t : T ⟶ G) (d : T ⟶ D) : G ⊗ T ⟶ G ⊗ D :=
  lift (translationFamilyMorphism G t) (snd G T ≫ d)

/-- Difference of the translated and unshifted original family classes. -/
def universalTranslationClass (t : T ⟶ G) (d : T ⟶ D)
    (a : PicardGroup (pullback G.hom D.hom)) : PicardGroup (pullback G.hom T.hom) :=
  pullbackClass (universalTranslationMorphism G t d).left a -
    pullbackClass (translationFamilyMap G d).left a

/-- The whole translated map commutes with every parameter morphism. -/
theorem universalTranslationMorphism_naturality (f : T' ⟶ T)
    (t : T ⟶ G) (d : T ⟶ D) :
    translationFamilyMap G f ≫ universalTranslationMorphism G t d =
      universalTranslationMorphism G (f ≫ t) (f ≫ d) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [universalTranslationMorphism, translationFamilyMorphism,
      translationFamilyMap, MonObj.comp_mul, Category.assoc]

/-- The original family action has its whole composition law. -/
theorem universalTranslationMorphism_comp (s t : T ⟶ G) (d : T ⟶ D) :
    universalTranslationMorphism G s (𝟙 T) ≫ universalTranslationMorphism G t d =
      universalTranslationMorphism G (s * t) d := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [universalTranslationMorphism, translationFamilyMorphism,
      MonObj.comp_mul, _root_.mul_assoc]

/-- Translation by the original unit is the unshifted family map. -/
theorem universalTranslationMorphism_one (d : T ⟶ D) :
    universalTranslationMorphism G (1 : T ⟶ G) d = translationFamilyMap G d := by
  simp [universalTranslationMorphism, translationFamilyMorphism, translationFamilyMap]

set_option backward.isDefEq.respectTransparency false in
/-- The class equation is natural on all original test schemes. -/
theorem universalTranslationClass_pullback (f : T' ⟶ T) (t : T ⟶ G)
    (d : T ⟶ D) (a : PicardGroup (pullback G.hom D.hom)) :
    pullbackClass ((familyScheme G.hom).map f) (universalTranslationClass G t d a) =
      universalTranslationClass G (f ≫ t) (f ≫ d) a := by
  rw [← translationFamilyMap_left]
  simp only [universalTranslationClass]
  simp only [← pullbackHom_apply, map_sub]
  simp only [pullbackHom_apply, ← pullbackClass_comp, ← Over.comp_left]
  rw [universalTranslationMorphism_naturality]
  have h : translationFamilyMap G f ≫ translationFamilyMap G d =
      translationFamilyMap G (f ≫ d) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [translationFamilyMap, Category.assoc]
  rw [h]

/-- The whole difference class vanishes at the translation unit. -/
theorem universalTranslationClass_one (d : T ⟶ D)
    (a : PicardGroup (pullback G.hom D.hom)) :
    universalTranslationClass G (1 : T ⟶ G) d a = 0 := by
  rw [universalTranslationClass, universalTranslationMorphism_one, sub_self]

/-- Translation is additive in the original family class. -/
theorem universalTranslationClass_add (t : T ⟶ G) (d : T ⟶ D)
    (a b : PicardGroup (pullback G.hom D.hom)) :
    universalTranslationClass G t d (a + b) =
      universalTranslationClass G t d a + universalTranslationClass G t d b := by
  simp only [universalTranslationClass, pullbackClass_add]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- For a source-normalized family, its translated difference restricts at
the original source unit to the original parameter evaluation. -/
theorem originRestriction_universalTranslationClass (t : T ⟶ G) (d : T ⟶ D)
    (a : PicardGroup (pullback G.hom D.hom))
    (ha : pullbackClass (lift (1 : D ⟶ G) (𝟙 D)).left a = 0) :
    pullbackClass (originSection G.hom η[G].left (Over.w η[G]) T)
        (universalTranslationClass G t d a) =
      pullbackClass (lift t d).left a := by
  rw [originSection_eq_unit_axis]
  have h₁ : lift (1 : T ⟶ G) (𝟙 T) ≫ universalTranslationMorphism G t d =
      lift t d := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [universalTranslationMorphism, translationFamilyMorphism, MonObj.comp_mul]
  have h₂ : lift (1 : T ⟶ G) (𝟙 T) ≫ translationFamilyMap G d =
      d ≫ lift (1 : D ⟶ G) (𝟙 D) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [translationFamilyMap]
  simp only [universalTranslationClass]
  simp only [← pullbackHom_apply, map_sub]
  simp only [pullbackHom_apply, ← pullbackClass_comp, ← Over.comp_left]
  rw [h₁, h₂, Over.comp_left, pullbackClass_comp, ha, pullbackClass_zero, sub_zero]

/-- Normalization subtracts precisely the original parameter evaluation. -/
theorem normalized_universalTranslationClass_val (t : T ⟶ G) (d : T ⟶ D)
    (a : PicardGroup (pullback G.hom D.hom))
    (ha : pullbackClass (lift (1 : D ⟶ G) (𝟙 D)).left a = 0) :
    (normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
      (universalTranslationClass G t d a)).val =
        universalTranslationClass G t d a -
          pullbackClass (pullback.snd G.hom T.hom) (pullbackClass (lift t d).left a) := by
  rw [normalizedFamilyClass_val, originRestriction_universalTranslationClass G t d a ha]

set_option backward.isDefEq.respectTransparency false in
/-- A family trivial on the parameter-unit axis stays trivial there after
every original translation. -/
theorem universalTranslationClass_parameter_one [MonObj D] (t : T ⟶ G)
    (a : PicardGroup (pullback G.hom D.hom))
    (ha : pullbackClass (lift (𝟙 G) (1 : G ⟶ D)).left a = 0) :
    universalTranslationClass G t (1 : T ⟶ D) a = 0 := by
  have h₁ : universalTranslationMorphism G t (1 : T ⟶ D) =
      translationFamilyMorphism G t ≫ lift (𝟙 G) (1 : G ⟶ D) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [universalTranslationMorphism]
  have h₂ : translationFamilyMap G (1 : T ⟶ D) =
      fst G T ≫ lift (𝟙 G) (1 : G ⟶ D) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [translationFamilyMap]
  simp only [universalTranslationClass, h₁, h₂, Over.comp_left, pullbackClass_comp,
    ha, pullbackClass_zero, sub_self]

/-- The same translated difference constructed as an actual line bundle. -/
def universalTranslationLineBundle (t : T ⟶ G) (d : T ⟶ D)
    (L : LineBundle (pullback G.hom D.hom)) : LineBundle (pullback G.hom T.hom) :=
  tensorLineBundle _ (pullbackLineBundle (universalTranslationMorphism G t d).left L)
    (dualLineBundle _ (pullbackLineBundle (translationFamilyMap G d).left L))

/-- The actual line-bundle constructor has the original difference class. -/
theorem classOf_universalTranslationLineBundle (t : T ⟶ G) (d : T ⟶ D)
    (L : LineBundle (pullback G.hom D.hom)) :
    classOf _ (universalTranslationLineBundle G t d L) =
      universalTranslationClass G t d (classOf _ L) := by
  simp only [universalTranslationLineBundle, classOf_tensor, classOf_dual,
    ← pullbackClass_classOf, universalTranslationClass, sub_eq_add_neg]
  rfl

end AlgebraicGeometry.Scheme.RelativePicard
