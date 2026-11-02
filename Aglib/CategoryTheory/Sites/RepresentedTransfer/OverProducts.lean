/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Actual pullback products in a full morphism-property Over category

The selected underlying pullbacks are retained. All comparisons are proved
at the original first and second projections, including the comparison to a
chosen categorical product; no definitional equality of product choices is used.
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

/-- The original identity arrow as terminal object of the full Over category. -/
abbrev productTerminal (X : C) : P.Over ⊤ X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (P.id_mem X)

/-- Base change followed by actual postcomposition, with variable first factor. -/
abbrev productTest (V : P.Over ⊤ X) : P.Over ⊤ X ⥤ P.Over ⊤ X :=
  pullback P ⊤ V.hom ⋙ map ⊤ V.prop

/-- The original first projection, equal to the native map/pullback counit. -/
def productFst (V U : P.Over ⊤ X) : (productTest P V).obj U ⟶ U :=
  (mapPullbackAdj P ⊤ V.hom V.prop trivial).counit.app U

/-- The second projection of the actual product test. -/
def productSnd (V U : P.Over ⊤ X) : (productTest P V).obj U ⟶ V :=
  MorphismProperty.Over.homMk
    (P := P)
    (pullback.snd U.hom V.hom) rfl (by trivial)

/-- Variation of the fixed factor of the actual product tests. -/
def productMap {V W : P.Over ⊤ X} (f : V ⟶ W) :
    productTest P V ⟶ productTest P W where
  app U := MorphismProperty.Over.homMk
    (P := P)
    (pullback.lift (pullback.fst U.hom V.hom)
      (pullback.snd U.hom V.hom ≫ f.left) (by
        rw [Category.assoc, MorphismProperty.Over.w f, pullback.condition])) (by
          change pullback.lift (pullback.fst U.hom V.hom)
            (pullback.snd U.hom V.hom ≫ f.left) _ ≫
              (pullback.snd U.hom W.hom ≫ W.hom) =
            pullback.snd U.hom V.hom ≫ V.hom
          rw [pullback.lift_snd_assoc, Category.assoc, MorphismProperty.Over.w f]) (by trivial)
  naturality U U' g := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift (pullback.fst U.hom V.hom ≫ g.left)
        (pullback.snd U.hom V.hom) _ ≫
          pullback.lift (pullback.fst U'.hom V.hom)
            (pullback.snd U'.hom V.hom ≫ f.left) _ =
      pullback.lift (pullback.fst U.hom V.hom)
          (pullback.snd U.hom V.hom ≫ f.left) _ ≫
        pullback.lift (pullback.fst U.hom W.hom ≫ g.left)
          (pullback.snd U.hom W.hom) _
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]

@[reassoc]
theorem productMap_fst {V W : P.Over ⊤ X} (f : V ⟶ W) (U : P.Over ⊤ X) :
    (productMap P f).app U ≫ productFst P W U = productFst P V U := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem productMap_snd {V W : P.Over ⊤ X} (f : V ⟶ W) (U : P.Over ⊤ X) :
    (productMap P f).app U ≫ productSnd P W U = productSnd P V U ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift (pullback.fst U.hom V.hom)
    (pullback.snd U.hom V.hom ≫ f.left) _ ≫ pullback.snd U.hom W.hom = _
  exact pullback.lift_snd _ _ _

/-- Literal interchange of the two factors. -/
def productSymmetry (V U : P.Over ⊤ X) :
    (productTest P V).obj U ≅ (productTest P U).obj V :=
  MorphismProperty.Over.isoMk
    (P := P) (pullbackSymmetry U.hom V.hom) (by
    change (pullbackSymmetry U.hom V.hom).hom ≫
      (pullback.snd V.hom U.hom ≫ U.hom) = pullback.snd U.hom V.hom ≫ V.hom
    rw [pullbackSymmetry_hom_comp_snd_assoc]
    exact pullback.condition)

@[reassoc]
theorem productSymmetry_snd (V U : P.Over ⊤ X) :
    (productSymmetry P V U).hom ≫ productSnd P U V = productFst P V U := by
  apply MorphismProperty.Over.Hom.ext
  exact pullbackSymmetry_hom_comp_snd _ _

/-- Symmetry respects variation of the actual test scheme. -/
@[reassoc]
theorem productSymmetry_naturality {V W : P.Over ⊤ X} (f : V ⟶ W) (U : P.Over ⊤ X) :
    (productSymmetry P V U).hom ≫ (productTest P U).map f =
      (productMap P f).app U ≫ (productSymmetry P W U).hom := by
  apply MorphismProperty.Over.Hom.ext
  change (pullbackSymmetry U.hom V.hom).hom ≫
      pullback.lift (pullback.fst V.hom U.hom ≫ f.left)
        (pullback.snd V.hom U.hom) _ =
    pullback.lift (pullback.fst U.hom V.hom)
        (pullback.snd U.hom V.hom ≫ f.left) _ ≫
      (pullbackSymmetry U.hom W.hom).hom
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
      pullbackSymmetry_hom_comp_fst_assoc]

/-- Multiplication by the original terminal test is the actual second projection. -/
def productTerminalIso (V : P.Over ⊤ X) :
    (productTest P V).obj (productTerminal P X) ≅ V :=
  MorphismProperty.Over.isoMk
    (P := P)
    (asIso (pullback.snd (𝟙 X) V.hom)) (by
      change pullback.snd (𝟙 X) V.hom ≫ V.hom = pullback.snd (𝟙 X) V.hom ≫ V.hom
      rfl)

@[simp]
theorem productTerminalIso_hom (V : P.Over ⊤ X) :
    (productTerminalIso P V).hom = productSnd P V (productTerminal P X) := by
  apply MorphismProperty.Over.Hom.ext
  rfl

/-- The inverse terminal comparison is natural in the test object. -/
@[reassoc]
theorem productTerminalIso_inv_naturality {V W : P.Over ⊤ X} (f : V ⟶ W) :
    (productTerminalIso P V).inv ≫ (productMap P f).app (productTerminal P X) =
      f ≫ (productTerminalIso P W).inv := by
  apply (cancel_mono (productTerminalIso P W).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [productTerminalIso_hom P, productMap_snd P,
    ← productTerminalIso_hom P, Iso.inv_hom_id_assoc]

/-- Symmetry followed by the first projection is the second projection. -/
@[reassoc]
theorem productSymmetry_counit (V U : P.Over ⊤ X) :
    (productSymmetry P V U).hom ≫ (mapPullbackAdj P ⊤ U.hom U.prop trivial).counit.app V =
      productSnd P V U := by
  apply MorphismProperty.Over.Hom.ext
  change (pullbackSymmetry U.hom V.hom).hom ≫ pullback.fst V.hom U.hom =
    pullback.snd U.hom V.hom
  exact pullbackSymmetry_hom_comp_fst _ _

/-- The represented augmentation, followed by terminal transport, is the same projection. -/
@[reassoc]
theorem productTest_terminal (V U : P.Over ⊤ X) :
    (productTest P V).map ((mkIdTerminal P X).from U) ≫
      (productTerminalIso P V).hom = productSnd P V U := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift (pullback.fst U.hom V.hom ≫ U.hom)
    (pullback.snd U.hom V.hom) _ ≫ pullback.snd (𝟙 X) V.hom = _
  exact pullback.lift_snd _ _ _

/-- The actual pullback projections form a binary product cone. -/
def productFan (V U : P.Over ⊤ X) : BinaryFan U V :=
  BinaryFan.mk (productFst P V U) (productSnd P V U)

/-- The complete universal property of the original pullback product. -/
def productFanIsLimit (V U : P.Over ⊤ X) : IsLimit (productFan P V U) := by
  let lift (s : BinaryFan U V) : s.pt ⟶ (productTest P V).obj U :=
    MorphismProperty.Over.homMk
      (pullback.lift s.fst.left s.snd.left
        ((MorphismProperty.Over.w s.fst).trans (MorphismProperty.Over.w s.snd).symm))
      (by
        change pullback.lift s.fst.left s.snd.left _ ≫
          (pullback.snd U.hom V.hom ≫ V.hom) = s.pt.hom
        rw [pullback.lift_snd_assoc]
        exact MorphismProperty.Over.w s.snd)
  refine BinaryFan.isLimitMk lift ?_ ?_ ?_
  · intro s
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  · intro s
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _
  · intro s m hfst hsnd
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · exact (congrArg (fun f => f.left) hfst).trans
        (pullback.lift_fst (f := U.hom) (g := V.hom) s.fst.left s.snd.left
          ((MorphismProperty.Over.w s.fst).trans (MorphismProperty.Over.w s.snd).symm)).symm
    · exact (congrArg (fun f => f.left) hsnd).trans
        (pullback.lift_snd (f := U.hom) (g := V.hom) s.fst.left s.snd.left
          ((MorphismProperty.Over.w s.fst).trans (MorphismProperty.Over.w s.snd).symm)).symm

/-- Compare to an existing selected product only through its universal property. -/
def productIso [HasBinaryProducts (P.Over ⊤ X)] (V U : P.Over ⊤ X) :
    (productTest P V).obj U ≅ U ⨯ V :=
  (productFanIsLimit P V U).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
theorem productIso_hom_fst [HasBinaryProducts (P.Over ⊤ X)] (V U : P.Over ⊤ X) :
    (productIso P V U).hom ≫ prod.fst = productFst P V U :=
  (productFanIsLimit P V U).conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨.left⟩

@[reassoc (attr := simp)]
theorem productIso_hom_snd [HasBinaryProducts (P.Over ⊤ X)] (V U : P.Over ⊤ X) :
    (productIso P V U).hom ≫ prod.snd = productSnd P V U :=
  (productFanIsLimit P V U).conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨.right⟩

end CategoryTheory.MorphismProperty.Over
