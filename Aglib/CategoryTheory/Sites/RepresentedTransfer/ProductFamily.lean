/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.RepresentedTransfer.OverProducts

/-! # The functor family of original pullback products

These laws retain `productTest` and `productMap`. Evaluating the family varies
the second factor; its comparison to variation of the first factor is the
original pullback symmetry, not a replacement choice of products.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe c h

namespace CategoryTheory.MorphismProperty.Over

variable {C : Type c} [Category.{h} C] [HasPullbacks C]
  (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  {X : C}

/-- Original product tests and original variation maps, bundled functorially. -/
def productFamily : P.Over ⊤ X ⥤ (P.Over ⊤ X ⥤ P.Over ⊤ X) where
  obj := productTest P
  map := productMap P
  map_id V := by
    apply NatTrans.ext
    funext T
    change (productMap P (𝟙 V)).app T = 𝟙 _
    apply BinaryFan.IsLimit.hom_ext (productFanIsLimit P V T)
    · change (productMap P (𝟙 V)).app T ≫ productFst P V T =
        𝟙 _ ≫ productFst P V T
      simp only [productMap_fst, Category.id_comp]
    · change (productMap P (𝟙 V)).app T ≫ productSnd P V T =
        𝟙 _ ≫ productSnd P V T
      simp only [productMap_snd, Category.id_comp, Category.comp_id]
  map_comp {V W Z} f g := by
    apply NatTrans.ext
    funext T
    change (productMap P (f ≫ g)).app T =
      (productMap P f).app T ≫ (productMap P g).app T
    apply BinaryFan.IsLimit.hom_ext (productFanIsLimit P Z T)
    · change (productMap P (f ≫ g)).app T ≫ productFst P Z T =
        ((productMap P f).app T ≫ (productMap P g).app T) ≫ productFst P Z T
      simp only [Category.assoc, productMap_fst]
    · change (productMap P (f ≫ g)).app T ≫ productSnd P Z T =
        ((productMap P f).app T ≫ (productMap P g).app T) ≫ productSnd P Z T
      simp only [Category.assoc, productMap_snd, productMap_snd_assoc]

/-- Evaluation of the actual product family at the first factor. -/
abbrev productFamilyEvaluation (T : P.Over ⊤ X) : P.Over ⊤ X ⥤ P.Over ⊤ X :=
  productFamily P ⋙ (evaluation _ _).obj T

/-- The original product symmetry compares the two possible varying factors. -/
def productFamilyEvaluationIso (T : P.Over ⊤ X) :
    productFamilyEvaluation P T ≅ productTest P T :=
  NatIso.ofComponents (fun V => productSymmetry P V T) (fun f =>
    (productSymmetry_naturality P f T).symm)

/-- Variation along a mono is mono on every original product test. -/
instance productMap_app_mono {V W : P.Over ⊤ X} (f : V ⟶ W) [Mono f]
    (T : P.Over ⊤ X) : Mono ((productMap P f).app T) where
  right_cancellation {Z} a b hab := by
    apply BinaryFan.IsLimit.hom_ext (productFanIsLimit P V T)
    · change a ≫ productFst P V T = b ≫ productFst P V T
      simpa only [Category.assoc, productMap_fst] using
        congrArg (fun k => k ≫ productFst P W T) hab
    · change a ≫ productSnd P V T = b ≫ productSnd P V T
      apply (cancel_mono f).1
      simpa only [Category.assoc, productMap_snd] using
        congrArg (fun k => k ≫ productSnd P W T) hab

instance productFamilyEvaluation_preservesMonomorphisms (T : P.Over ⊤ X) :
    (productFamilyEvaluation P T).PreservesMonomorphisms where
  preserves f _ := inferInstanceAs (Mono ((productMap P f).app T))

end CategoryTheory.MorphismProperty.Over
