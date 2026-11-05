/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.RepresentedTransfer.ProductProjectionNaturality
public import Aglib.CategoryTheory.Sites.RepresentedTransfer.OverProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Canonical base change of the original represented product tests

The comparison retains the actual pullback products. Its two projection laws
and fixed-factor naturality identify the original face maps, independently of
any sheaf or derived-category model.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.MorphismProperty.Over
universe c h d k
variable {C : Type c} [Category.{h} C] [HasPullbacks C]
  {D : Type d} [Category.{k} D] [HasPullbacks D]
  (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  (Q : MorphismProperty D) [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
  {X : C} {Y : D}
  [HasBinaryProducts (P.Over ⊤ X)] [HasBinaryProducts (Q.Over ⊤ Y)]
  (F : P.Over ⊤ X ⥤ Q.Over ⊤ Y) [PreservesLimitsOfShape (Discrete WalkingPair) F]

/-- Original product-test transport, characterized by both projections. -/
def productBaseChangeIso (V U : P.Over ⊤ X) :
    F.obj ((productTest P V).obj U) ≅ (productTest Q (F.obj V)).obj (F.obj U) :=
  F.mapIso (productIso P V U) ≪≫ PreservesLimitPair.iso F U V ≪≫
    (productIso Q (F.obj V) (F.obj U)).symm

@[reassoc (attr := simp)]
theorem productBaseChangeIso_fst (V U : P.Over ⊤ X) :
    (productBaseChangeIso P Q F V U).hom ≫ productFst Q (F.obj V) (F.obj U) =
      F.map (productFst P V U) := by
  simp only [productBaseChangeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    PreservesLimitPair.iso_hom]
  rw [← productIso_hom_fst Q (F.obj V) (F.obj U)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, prodComparison_fst]
  rw [← F.map_comp, productIso_hom_fst]

@[reassoc (attr := simp)]
theorem productBaseChangeIso_snd (V U : P.Over ⊤ X) :
    (productBaseChangeIso P Q F V U).hom ≫ productSnd Q (F.obj V) (F.obj U) =
      F.map (productSnd P V U) := by
  simp only [productBaseChangeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    PreservesLimitPair.iso_hom]
  rw [← productIso_hom_snd Q (F.obj V) (F.obj U)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, prodComparison_snd]
  rw [← F.map_comp, productIso_hom_snd]

/-- Naturality in the variable original test. -/
@[reassoc]
theorem productBaseChangeIso_naturality (V : P.Over ⊤ X)
    {U W : P.Over ⊤ X} (a : U ⟶ W) :
    F.map ((productTest P V).map a) ≫ (productBaseChangeIso P Q F V W).hom =
      (productBaseChangeIso P Q F V U).hom ≫ (productTest Q (F.obj V)).map (F.map a) := by
  apply (cancel_mono (productIso Q (F.obj V) (F.obj W)).hom).1
  apply prod.hom_ext
  · simp only [Category.assoc, productIso_hom_fst, productBaseChangeIso_fst,
      productTest_map_fst, productBaseChangeIso_fst_assoc, ← F.map_comp]
  · simp only [Category.assoc, productIso_hom_snd, productBaseChangeIso_snd,
      productTest_map_snd, ← F.map_comp]

/-- Natural transport of the actual product-test functor. -/
def productBaseChangeNatIso (V : P.Over ⊤ X) :
    productTest P V ⋙ F ≅ F ⋙ productTest Q (F.obj V) :=
  NatIso.ofComponents (productBaseChangeIso P Q F V)
    (fun a => productBaseChangeIso_naturality P Q F V a)

/-- The original fixed-factor face is preserved by product base change. -/
@[reassoc]
theorem productBaseChangeIso_face {V W : P.Over ⊤ X} (a : V ⟶ W)
    (U : P.Over ⊤ X) :
    F.map ((productMap P a).app U) ≫ (productBaseChangeIso P Q F W U).hom =
      (productBaseChangeIso P Q F V U).hom ≫ (productMap Q (F.map a)).app (F.obj U) := by
  apply (cancel_mono (productIso Q (F.obj W) (F.obj U)).hom).1
  apply prod.hom_ext
  · simp only [Category.assoc, productIso_hom_fst, productBaseChangeIso_fst,
      productMap_fst, ← F.map_comp]
  · simp only [Category.assoc, productIso_hom_snd, productBaseChangeIso_snd,
      productMap_snd, productBaseChangeIso_snd_assoc, ← F.map_comp]

/-- The inverse comparison preserves the same original fixed-factor face. -/
@[reassoc]
theorem productBaseChangeIso_inv_face {V W : P.Over ⊤ X} (a : V ⟶ W)
    (U : P.Over ⊤ X) :
    (productBaseChangeIso P Q F V U).inv ≫ F.map ((productMap P a).app U) =
      (productMap Q (F.map a)).app (F.obj U) ≫ (productBaseChangeIso P Q F W U).inv := by
  apply (cancel_mono (productBaseChangeIso P Q F W U).hom).1
  rw [Category.assoc, productBaseChangeIso_face, Iso.inv_hom_id_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.MorphismProperty.Over
