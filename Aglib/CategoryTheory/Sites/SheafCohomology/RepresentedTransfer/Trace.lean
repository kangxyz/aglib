/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.RepresentedTransfer.OverProducts
public import Aglib.CategoryTheory.Sites.Hypercohomology.RepresentableTransfer
public import Mathlib.CategoryTheory.Sites.Continuous

/-! # The represented restriction trace on actual pullback product tests

The original free arrow acts on the same coefficient after product symmetry;
the terminal product comparison returns to the original section group. Both
naturalities and the original unit/rank law follow from these three factors.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty.Over

namespace CategoryTheory.Sheaf.Hypercohomology

universe c h t

variable {C : Type c} [Category.{h} C] [HasPullbacks C]
  (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  {X : C} (J : GrothendieckTopology (P.Over ⊤ X))
  [HasSheafify J AddCommGrpCat.{max h t}]
  [∀ V : P.Over ⊤ X, (productTest P V).IsContinuous J J]

/-- Original coefficients evaluated on the actual selected product tests. -/
abbrev productSheaf (V : P.Over ⊤ X) :
    Sheaf J AddCommGrpCat.{max h t} ⥤ Sheaf J AddCommGrpCat.{max h t} :=
  (productTest P V).sheafPushforwardContinuous AddCommGrpCat.{max h t} J J

/-- Variation of the product-test coefficient retains the actual site map. -/
def productSheafMap {V W : P.Over ⊤ X} (f : V ⟶ W) :
    productSheaf P J W ⟶ productSheaf P J V :=
  Functor.sheafPushforwardContinuousNatTrans (productMap P f) AddCommGrpCat.{max h t} J J

/-- The product unit is restriction along the original first projection. -/
def productUnit (U : P.Over ⊤ X) :
    𝟭 (Sheaf J AddCommGrpCat.{max h t}) ⟶ productSheaf P J U :=
  Functor.sheafPushforwardContinuousNatTrans
    (mapPullbackAdj P ⊤ U.hom U.prop trivial).counit AddCommGrpCat.{max h t} J J

variable (U : P.Over ⊤ X)
  (a : freeAbelianSheaf.{t} J (productTerminal P X) ⟶ freeAbelianSheaf.{t} J U)

/-- Evaluation of a fixed represented transfer on original product-test sheaves. -/
def representedRestrictionTrace :
    productSheaf P J U ⟶ 𝟭 (Sheaf J AddCommGrpCat.{max h t}) where
  app F := ⟨{
    app V := F.obj.map (productSymmetry P V.unop U).hom.op ≫
      (representedSectionsMap J a).app
        ((productSheaf P J V.unop).obj F) ≫
      F.obj.map (productTerminalIso P V.unop).inv.op
    naturality V W f := by
      let R := representedSectionsMap J a
      have hs :
          F.obj.map ((productTest P U).map f.unop).op ≫
            F.obj.map (productSymmetry P W.unop U).hom.op =
          F.obj.map (productSymmetry P V.unop U).hom.op ≫
            F.obj.map ((productMap P f.unop).app U).op := by
        rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp,
          productSymmetry_naturality P]
      have ht :
          F.obj.map ((productMap P f.unop).app (productTerminal P X)).op ≫
            F.obj.map (productTerminalIso P W.unop).inv.op =
          F.obj.map (productTerminalIso P V.unop).inv.op ≫ F.obj.map f := by
        simpa only [op_comp, F.obj.map_comp, Quiver.Hom.op_unop] using
          congrArg (fun k => F.obj.map k.op)
            (productTerminalIso_inv_naturality P f.unop)
      have hr := R.naturality ((productSheafMap P J f.unop).app F)
      change F.obj.map ((productTest P U).map f.unop).op ≫
          (F.obj.map (productSymmetry P W.unop U).hom.op ≫
            R.app ((productSheaf P J W.unop).obj F) ≫
            F.obj.map (productTerminalIso P W.unop).inv.op) =
        (F.obj.map (productSymmetry P V.unop U).hom.op ≫
          R.app ((productSheaf P J V.unop).obj F) ≫
          F.obj.map (productTerminalIso P V.unop).inv.op) ≫ F.obj.map f
      change F.obj.map ((productMap P f.unop).app U).op ≫
          R.app ((productSheaf P J W.unop).obj F) =
        R.app ((productSheaf P J V.unop).obj F) ≫
          F.obj.map ((productMap P f.unop).app (productTerminal P X)).op at hr
      exact ((CommSq.mk hs.symm).horiz_comp
        ((CommSq.mk hr.symm).horiz_comp (CommSq.mk ht.symm))).w.symm }⟩
  naturality F G g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    have hs := g.hom.naturality (productSymmetry P V.unop U).hom.op
    have ht := g.hom.naturality (productTerminalIso P V.unop).inv.op
    have hr := (representedSectionsMap J a).naturality
      ((productSheaf P J V.unop).map g)
    change g.hom.app (op ((productTest P U).obj V.unop)) ≫
        (G.obj.map (productSymmetry P V.unop U).hom.op ≫ _ ≫ _) =
      (F.obj.map (productSymmetry P V.unop U).hom.op ≫ _ ≫ _) ≫ g.hom.app V
    change g.hom.app (op ((productTest P V.unop).obj U)) ≫
        (representedSectionsMap J a).app
          ((productSheaf P J V.unop).obj G) =
      (representedSectionsMap J a).app
          ((productSheaf P J V.unop).obj F) ≫
        g.hom.app (op ((productTest P V.unop).obj (productTerminal P X))) at hr
    exact ((CommSq.mk hs).horiz_comp
      ((CommSq.mk hr.symm).horiz_comp (CommSq.mk ht))).w.symm

/-- The trace is exactly symmetry, the original represented section map, then
inverse terminal transport, in that order. -/
theorem representedRestrictionTrace_app
    (F : Sheaf J AddCommGrpCat.{max h t}) (V : P.Over ⊤ X) :
    ((representedRestrictionTrace P J U a).app F).hom.app (op V) =
      F.obj.map (productSymmetry P V U).hom.op ≫
        (representedSectionsMap J a).app ((productSheaf P J V).obj F) ≫
        F.obj.map (productTerminalIso P V).inv.op := rfl

/-- The represented rank relation gives the actual restriction-adjunction unit relation. -/
theorem representedRestrictionTrace_rank (n : ℕ)
    (ha : a ≫ (freeAbelianSheafFunctor.{t} J).map
      ((mkIdTerminal P X).from U) = n • 𝟙 _)
    (F : Sheaf J AddCommGrpCat.{max h t}) :
    (productUnit P J U).app F ≫
        (representedRestrictionTrace P J U a).app F = n • 𝟙 F := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let R := representedSectionsMap J a
  let e := productTerminalIso P V.unop
  let r : F.obj.obj (op ((productTest P V.unop).obj U)) ⟶
      F.obj.obj (op ((productTest P V.unop).obj (productTerminal P X))) :=
    R.app ((productSheaf P J V.unop).obj F)
  let m : F.obj.obj (op ((productTest P V.unop).obj (productTerminal P X))) ⟶
      F.obj.obj (op ((productTest P V.unop).obj U)) :=
    F.obj.map ((productTest P V.unop).map ((mkIdTerminal P X).from U)).op
  have hp :
      F.obj.map (productFst P U V.unop).op ≫
        F.obj.map (productSymmetry P V.unop U).hom.op =
      F.obj.map e.hom.op ≫ m := by
    change F.obj.map
        ((mapPullbackAdj P ⊤ U.hom U.prop trivial).counit.app V.unop).op ≫
      F.obj.map (productSymmetry P V.unop U).hom.op = F.obj.map e.hom.op ≫ m
    rw [← F.obj.map_comp, ← op_comp, productSymmetry_counit P]
    change F.obj.map (productSnd P V.unop U).op =
      F.obj.map e.hom.op ≫
        F.obj.map ((productTest P V.unop).map ((mkIdTerminal P X).from U)).op
    rw [← F.obj.map_comp, ← op_comp, productTest_terminal P]
  have hr := representedSectionsMap_rank J a
    ((mkIdTerminal P X).from U) n ha ((productSheaf P J V.unop).obj F)
  change m ≫ r =
    n • 𝟙 (F.obj.obj (op ((productTest P V.unop).obj (productTerminal P X)))) at hr
  change F.obj.map
      (productFst P U V.unop).op ≫
      (F.obj.map (productSymmetry P V.unop U).hom.op ≫ r ≫ F.obj.map e.inv.op) =
        n • 𝟙 (F.obj.obj V)
  rw [← Category.assoc, hp, Category.assoc, ← Category.assoc _ _ (F.obj.map e.inv.op), hr]
  rw [Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
    ← F.obj.map_comp, ← op_comp, e.inv_hom_id, op_id, F.obj.map_id]

end CategoryTheory.Sheaf.Hypercohomology
