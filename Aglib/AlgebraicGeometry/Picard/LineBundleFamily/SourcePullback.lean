/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Presheaf.Pullback
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Translation

/-!
# Source pullback of the original translated line-bundle family

The original source-family map is the native product morphism. Its whole
translation formula, Picard-class formula and parameter naturality hold for
an arbitrary source morphism and arbitrary parameter scheme. In particular
the source morphism need not be flat. Inversion of the coefficient and of
the parameter gives the original difference family, with its order and
constant source coefficient retained explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
  (G : Over (Spec (.of k))) [GrpObj G]

omit [GrpObj G] in
set_option backward.isDefEq.respectTransparency false in
/-- The original Picard source-family map is the native product of the
original source map with the identity on the parameter. -/
theorem familyMapOfHom_eq_tensorHom (f : X ⟶ G) (T : Over (Spec (.of k))) :
    familyMapOfHom f T = (f ⊗ₘ 𝟙 T).left := by
  apply pullback.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- Whole source-pullback formula for the actual translation morphism,
before passing to line bundles or evaluating any test point. -/
theorem familyMapOfHom_comp_translationFamilyMorphism (f : X ⟶ G)
    {T : Over (Spec (.of k))} (t : T ⟶ G) :
    familyMapOfHom f T ≫ (translationFamilyMorphism G t).left =
      ((fst X T ≫ f) * (snd X T ≫ t)).left := by
  rw [familyMapOfHom_eq_tensorHom, ← Over.comp_left]
  congr 1
  simp only [translationFamilyMorphism, MonObj.comp_mul,
    tensorHom_fst, tensorHom_snd_assoc, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of the original translated class along any source morphism. -/
theorem pullbackClass_familyMapOfHom_translationFamilyClass (f : X ⟶ G)
    {T : Over (Spec (.of k))} (t : T ⟶ G) (a : PicardGroup G.left) :
    pullbackClass (familyMapOfHom f T) (translationFamilyClass G t a) =
      pullbackClass ((fst X T ≫ f) * (snd X T ≫ t)).left a -
        pullbackClass (fst X T).left (pullbackClass f.left a) := by
  simp only [translationFamilyClass, ← pullbackHom_apply, map_sub]
  simp only [pullbackHom_apply, ← pullbackClass_comp]
  rw [familyMapOfHom_comp_translationFamilyMorphism]
  congr 1
  exact congrArg (fun v => pullbackClass v a) (familyMapOfHom_fst f T)

set_option backward.isDefEq.respectTransparency false in
/-- The same source-pullback class formula commutes with every original
parameter morphism, including maps of nonreduced test schemes. -/
theorem pullbackClass_familyMapOfHom_translationFamilyClass_naturality (f : X ⟶ G)
    {T T' : Over (Spec (.of k))} (b : T' ⟶ T) (t : T ⟶ G)
    (a : PicardGroup G.left) :
    pullbackClass ((familyScheme X.hom).map b)
        (pullbackClass (familyMapOfHom f T) (translationFamilyClass G t a)) =
      pullbackClass (familyMapOfHom f T') (translationFamilyClass G (b ≫ t) a) := by
  rw [← pullbackClass_comp, familyMapOfHom_naturality, pullbackClass_comp,
    translationFamilyClass_pullback]

set_option backward.isDefEq.respectTransparency false in
/-- Invert both the coefficient coordinate and the translating parameter:
the resulting whole morphism is parameter minus source. This law uses only
the group object and does not require commutativity. -/
theorem familyMapOfHom_comp_translationFamilyMorphism_inv (f : X ⟶ G)
    {T : Over (Spec (.of k))} (t : T ⟶ G) :
    familyMapOfHom f T ≫ (translationFamilyMorphism G (t ≫ ι[G])).left ≫ ι[G].left =
      ((snd X T ≫ t) / (fst X T ≫ f)).left := by
  rw [← Category.assoc, familyMapOfHom_comp_translationFamilyMorphism, ← Over.comp_left]
  change (((fst X T ≫ f) * (snd X T ≫ t)⁻¹)⁻¹).left = _
  rw [_root_.mul_inv_rev, inv_inv, div_eq_mul_inv]

set_option backward.isDefEq.respectTransparency false in
/-- The exact difference-family class, including its original constant
source coefficient. Inversion pullback is not dualization of a line bundle. -/
theorem pullbackClass_familyMapOfHom_translationFamilyClass_inv (f : X ⟶ G)
    {T : Over (Spec (.of k))} (t : T ⟶ G) (a : PicardGroup G.left) :
    pullbackClass (familyMapOfHom f T)
        (translationFamilyClass G (t ≫ ι[G]) (pullbackClass ι[G].left a)) =
      pullbackClass ((snd X T ≫ t) / (fst X T ≫ f)).left a -
        pullbackClass (fst X T).left (pullbackClass f.left (pullbackClass ι[G].left a)) := by
  rw [pullbackClass_familyMapOfHom_translationFamilyClass]
  congr 1
  rw [← pullbackClass_comp, ← Over.comp_left]
  change pullbackClass (((fst X T ≫ f) * (snd X T ≫ t)⁻¹)⁻¹).left a = _
  rw [_root_.mul_inv_rev, inv_inv, div_eq_mul_inv]

end AlgebraicGeometry.Scheme.RelativePicard
