/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Morphism

/-!
# The anti-diagonal identity on the scheme-valued kernel

For any locally Noetherian test scheme mapping to the kernel of `φ_L`, the
original pulled-back line bundle tensored with its inverse-parameter pullback
is trivial. The argument uses the entire normalized family on `G × T`, not
just a statement on geometric points. It therefore applies to nonreduced
kernel schemes without assuming smoothness or dimension of the dual Picard
object. This is the line-bundle input to the ample-kernel argument of
Edixhoven--van der Geer--Moonen, Chapter II, (2.17)(iii) and (2.19), pp. 22–23.
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
  [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- On a scheme-valued kernel point, the entire translated family is the
pullback of the original origin restriction. -/
theorem translationFamilyClass_eq_base_of_comp_lineBundleClassMorphism_eq_one
    {T : LocallyNoetherianOver (Spec (.of k))} (t : T.obj ⟶ G)
    (a : PicardGroup G.left) (ht : letI := picardCommGrpObj G.hom P R
      t ≫ lineBundleClassMorphism G P R a = 1) :
    translationFamilyClass G t a =
      pullbackClass (pullback.snd G.hom T.obj.hom) (pullbackClass t.left a) := by
  let := picardCommGrpObj G.hom P R
  have h := normalizedRepresentableBy_homEquiv_one
    G.hom η[G].left (Over.w η[G]) P R T
  rw [← ht, homEquiv_comp_lineBundleClassMorphism] at h
  have hv := congrArg Subtype.val h
  rw [normalized_translationFamilyClass_val] at hv
  exact sub_eq_zero.mp hv

/-- The anti-diagonal identity holds on every locally Noetherian kernel
test scheme, including schemes with nilpotents. -/
theorem pullbackClass_add_inverse_eq_zero_of_comp_lineBundleClassMorphism_eq_one
    {T : LocallyNoetherianOver (Spec (.of k))} (t : T.obj ⟶ G)
    (a : PicardGroup G.left) (ht : letI := picardCommGrpObj G.hom P R
      t ≫ lineBundleClassMorphism G P R a = 1) :
    pullbackClass t.left a + pullbackClass t⁻¹.left a = 0 := by
  let := picardCommGrpObj G.hom P R
  have h := translationFamilyClass_eq_base_of_comp_lineBundleClassMorphism_eq_one
    G P R t a ht
  have hm : lift t⁻¹ (𝟙 T.obj) ≫ translationFamilyMorphism G t = 1 := by
    simp only [translationFamilyMorphism, MonObj.comp_mul, lift_fst,
      lift_snd_assoc, Category.id_comp, _root_.inv_mul_cancel]
  have hp := congrArg (pullbackClass (lift t⁻¹ (𝟙 T.obj)).left) h
  change pullbackClass (lift t⁻¹ (𝟙 T.obj)).left
      (translationFamilyClass G t a) =
    pullbackClass (lift t⁻¹ (𝟙 T.obj)).left
      (pullbackClass (snd G T.obj).left (pullbackClass t.left a)) at hp
  simp only [translationFamilyClass] at hp
  simp only [← pullbackHom_apply, map_sub] at hp
  simp only [pullbackHom_apply, ← pullbackClass_comp,
    ← Over.comp_left, hm, lift_fst, lift_snd_assoc, Category.id_comp,
    Group.LineBundleCube.pullbackClass_one, zero_sub] at hp
  exact eq_neg_iff_add_eq_zero.mp hp.symm

/-- The preceding class identity is an isomorphism of the original tensor
line bundle with the trivial line bundle on the parameter scheme. -/
theorem nonempty_tensor_pullback_inverse_iso_trivial_of_comp_lineBundleMorphism_eq_one
    {T : LocallyNoetherianOver (Spec (.of k))} (t : T.obj ⟶ G)
    (L : LineBundle G.left) (ht : letI := picardCommGrpObj G.hom P R
      t ≫ lineBundleMorphism G P R L = 1) :
    Nonempty ((tensorLineBundle T.obj.left (pullbackLineBundle t.left L)
      (pullbackLineBundle t⁻¹.left L)).val ≅ (trivialLineBundle T.obj.left).val) := by
  let := picardCommGrpObj G.hom P R
  apply (class_eq_iff _ _ _).mp
  change classOf T.obj.left (tensorLineBundle T.obj.left (pullbackLineBundle t.left L)
      (pullbackLineBundle t⁻¹.left L)) = classOf T.obj.left (trivialLineBundle T.obj.left)
  rw [classOf_tensor, classOf_trivial, ← pullbackClass_classOf, ← pullbackClass_classOf]
  exact pullbackClass_add_inverse_eq_zero_of_comp_lineBundleClassMorphism_eq_one
    G P R t (classOf G.left L) ht

end AlgebraicGeometry.Scheme.RelativePicard
