/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Normalized
public import Aglib.AlgebraicGeometry.Group.LineBundleCube.Basic

/-!
# The original family of translated line bundles

For a group scheme `G` over a field, an actual map `t : T ⟶ G` acts by right
translation on `G × T`. The family class is `t_t^* L_T - L_T`. Its normalization
at the original unit is the Mumford class `t_t^* L_T - L_T - pr₂^* t^* L`.
These identities hold on every test scheme, including nonreduced schemes.
No Picard representability, properness or smoothness is needed here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

/-- The original family map of right translation by a test-scheme point. -/
def translationFamilyMorphism {T : Over (Spec (.of k))} (t : T ⟶ G) : G ⊗ T ⟶ G :=
  fst G T * (snd G T ≫ t)

/-- The family of translated classes before normalization. -/
def translationFamilyClass {T : Over (Spec (.of k))} (t : T ⟶ G)
    (a : PicardGroup G.left) : PicardGroup (pullback G.hom T.hom) :=
  pullbackClass (translationFamilyMorphism G t).left a -
    pullbackClass (fst G T).left a

/-- The original map between two parameterized products. -/
def translationFamilyMap {T T' : Over (Spec (.of k))} (f : T' ⟶ T) : G ⊗ T' ⟶ G ⊗ T :=
  lift (fst G T') (snd G T' ≫ f)

omit [GrpObj G] in
set_option backward.isDefEq.respectTransparency false in
/-- The product map used for translations is the existing Picard family map. -/
theorem translationFamilyMap_left {T T' : Over (Spec (.of k))} (f : T' ⟶ T) :
    (translationFamilyMap G f).left = (familyScheme G.hom).map f := by
  apply pullback.hom_ext <;> simp [translationFamilyMap, familyScheme_map, pullback.map]

/-- Right translations of families commute with every original parameter map. -/
theorem translationFamilyMap_comp_translationFamilyMorphism
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T ⟶ G) :
    translationFamilyMap G f ≫ translationFamilyMorphism G t =
      translationFamilyMorphism G (f ≫ t) := by
  simp only [translationFamilyMorphism, MonObj.comp_mul, translationFamilyMap,
    lift_fst, lift_snd_assoc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of the whole translated family is the translated pullback family. -/
theorem translationFamilyClass_pullback {T T' : Over (Spec (.of k))}
    (f : T' ⟶ T) (t : T ⟶ G) (a : PicardGroup G.left) :
    pullbackClass ((familyScheme G.hom).map f) (translationFamilyClass G t a) =
      translationFamilyClass G (f ≫ t) a := by
  rw [← translationFamilyMap_left]
  simp only [translationFamilyClass]
  simp only [← pullbackHom_apply, map_sub]
  simp only [pullbackHom_apply, ← pullbackClass_comp, ← Over.comp_left]
  rw [translationFamilyMap_comp_translationFamilyMorphism]
  simp only [translationFamilyMap, lift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- The section used by Picard normalization is the original group-unit axis. -/
theorem originSection_eq_unit_axis (T : Over (Spec (.of k))) :
    originSection G.hom η[G].left (Over.w η[G]) T =
      (lift (1 : T ⟶ G) (𝟙 T)).left := by
  apply pullback.hom_ext <;>
    simp [originSection, Hom.one_def, Over.comp_left]

/-- Translation sends the original unit axis to its parameter. -/
theorem unit_axis_comp_translationFamilyMorphism {T : Over (Spec (.of k))} (t : T ⟶ G) :
    lift (1 : T ⟶ G) (𝟙 T) ≫ translationFamilyMorphism G t = t := by
  simp only [translationFamilyMorphism, MonObj.comp_mul, lift_fst,
    lift_snd_assoc, Category.id_comp, _root_.one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The origin restriction of the translated family is the pullback of its
original line-bundle class by the parameter. -/
theorem originRestriction_translationFamilyClass {T : Over (Spec (.of k))}
    (t : T ⟶ G) (a : PicardGroup G.left) :
    pullbackClass (originSection G.hom η[G].left (Over.w η[G]) T)
      (translationFamilyClass G t a) = pullbackClass t.left a := by
  rw [originSection_eq_unit_axis]
  simp only [translationFamilyClass]
  simp only [← pullbackHom_apply, map_sub]
  simp only [pullbackHom_apply, ← pullbackClass_comp, ← Over.comp_left,
    unit_axis_comp_translationFamilyMorphism, lift_fst,
    Group.LineBundleCube.pullbackClass_one, sub_zero]

/-- The normalized translated family is the original Mumford class. -/
theorem normalized_translationFamilyClass_val {T : Over (Spec (.of k))}
    (t : T ⟶ G) (a : PicardGroup G.left) :
    (normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
      (translationFamilyClass G t a)).val =
        translationFamilyClass G t a -
          pullbackClass (pullback.snd G.hom T.hom) (pullbackClass t.left a) := by
  rw [normalizedFamilyClass_val, originRestriction_translationFamilyClass]

/-- The normalized family at the constant group identity vanishes on every
parameter scheme. -/
theorem translationFamilyClass_one (T : Over (Spec (.of k))) (a : PicardGroup G.left) :
    translationFamilyClass G (1 : T ⟶ G) a = 0 := by
  have h : translationFamilyMorphism G (1 : T ⟶ G) = fst G T := by
    simp only [translationFamilyMorphism, MonObj.comp_one, _root_.mul_one]
  simp only [translationFamilyClass, h, sub_self]

/-- Additivity in the original Picard class is independent of a selected
line-bundle representative. -/
theorem translationFamilyClass_add {T : Over (Spec (.of k))} (t : T ⟶ G)
    (a b : PicardGroup G.left) :
    translationFamilyClass G t (a + b) =
      translationFamilyClass G t a + translationFamilyClass G t b := by
  simp only [translationFamilyClass, pullbackClass_add]
  abel

@[simp]
theorem translationFamilyClass_zero {T : Over (Spec (.of k))} (t : T ⟶ G) :
    translationFamilyClass G t 0 = 0 := by
  simp only [translationFamilyClass, pullbackClass_zero, sub_self]

/-- The original universal translated family on `G × G`. -/
theorem translationFamilyClass_id (a : PicardGroup G.left) :
    translationFamilyClass G (𝟙 G) a =
      pullbackClass μ[G].left a - pullbackClass (fst G G).left a := by
  have h : translationFamilyMorphism G (𝟙 G) = μ[G] := by
    simp only [translationFamilyMorphism, Category.comp_id, Hom.mul_def,
      lift_fst_snd, Category.id_comp]
  rw [translationFamilyClass, h]

/-- The actual translated line-bundle family, before normalization. -/
def translationFamilyLineBundle {T : Over (Spec (.of k))} (t : T ⟶ G)
    (L : LineBundle G.left) : LineBundle (pullback G.hom T.hom) :=
  tensorLineBundle _ (pullbackLineBundle (translationFamilyMorphism G t).left L)
    (dualLineBundle _ (pullbackLineBundle (fst G T).left L))

/-- The actual bundle constructor has exactly the original translated class. -/
theorem classOf_translationFamilyLineBundle {T : Over (Spec (.of k))} (t : T ⟶ G)
    (L : LineBundle G.left) :
    classOf _ (translationFamilyLineBundle G t L) =
      translationFamilyClass G t (classOf _ L) := by
  simp only [translationFamilyLineBundle, classOf_tensor, classOf_dual,
    ← pullbackClass_classOf, translationFamilyClass, sub_eq_add_neg]

end AlgebraicGeometry.Scheme.RelativePicard
