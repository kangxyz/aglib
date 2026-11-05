/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.RepresentedTransfer.ProductProjectionNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.RepresentedTransfer.Trace
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# The original represented transfer on a splitting chart

The local free-representable sum relation determines the whole
coefficient-natural restriction trace. Its summands are restrictions along the
actual graphs in the original pullback products. The proof uses their original
product fan, without choosing a second product realization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe c h t i

namespace CategoryTheory.MorphismProperty.Over

variable {C : Type c} [Category.{h} C] [HasPullbacks C]
  (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  {X : C}

/-- The graph in the original product fan, with first projection the identity. -/
def productGraph {V U : P.Over ⊤ X} (f : V ⟶ U) : V ⟶ (productTest P U).obj V :=
  BinaryFan.IsLimit.lift (productFanIsLimit P U V) (𝟙 V) f

@[reassoc]
theorem productGraph_fst {V U : P.Over ⊤ X} (f : V ⟶ U) :
    productGraph P f ≫ productFst P U V = 𝟙 V :=
  BinaryFan.IsLimit.lift_fst (productFanIsLimit P U V) (𝟙 V) f

@[reassoc]
theorem productGraph_snd {V U : P.Over ⊤ X} (f : V ⟶ U) :
    productGraph P f ≫ productSnd P U V = f :=
  BinaryFan.IsLimit.lift_snd (productFanIsLimit P U V) (𝟙 V) f

/-- The diagonal followed by the terminal product map is the original inverse
terminal comparison. -/
theorem productGraph_terminal (V : P.Over ⊤ X) :
    productGraph P (𝟙 V) ≫ (productTest P V).map ((mkIdTerminal P X).from V) =
      (productTerminalIso P V).inv := by
  apply (cancel_mono (productTerminalIso P V).hom).mp
  rw [Category.assoc, productTest_terminal P, productGraph_snd, Iso.inv_hom_id]

/-- A graph is the original diagonal, the map on the first factor, and symmetry. -/
theorem productGraph_diagonal_map_symmetry {V U : P.Over ⊤ X} (f : V ⟶ U) :
    productGraph P (𝟙 V) ≫ (productTest P V).map f ≫ (productSymmetry P V U).hom =
      productGraph P f := by
  apply BinaryFan.IsLimit.hom_ext (productFanIsLimit P U V)
  · change _ ≫ productFst P U V = _ ≫ productFst P U V
    have hs : (productSymmetry P V U).hom ≫ productFst P U V = productSnd P V U :=
      productSymmetry_counit P V U
    simp only [Category.assoc, hs, productTest_map_snd, productGraph_snd, productGraph_fst]
  · change _ ≫ productSnd P U V = _ ≫ productSnd P U V
    rw [Category.assoc, Category.assoc, productSymmetry_snd, productTest_map_fst,
      productGraph_fst_assoc, productGraph_snd]

end CategoryTheory.MorphismProperty.Over

namespace CategoryTheory.Sheaf.Hypercohomology

section RepresentedSections

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max h t}]

/-- The original represented section transformation is additive in its free arrow. -/
def representedSectionsMapAddHom {T U : C} :
    (freeAbelianSheaf.{t} J T ⟶ freeAbelianSheaf.{t} J U) →+
      ((sheafSections J AddCommGrpCat.{max h t}).obj (op U) ⟶
        (sheafSections J AddCommGrpCat.{max h t}).obj (op T)) where
  toFun := representedSectionsMap J
  map_zero' := by
    ext F x
    change sectionsAddEquiv J T F (0 ≫ (sectionsAddEquiv J U F).symm x) = 0
    rw [zero_comp, map_zero]
  map_add' a b := by
    ext F x
    change sectionsAddEquiv J T F ((a + b) ≫ (sectionsAddEquiv J U F).symm x) =
      sectionsAddEquiv J T F (a ≫ (sectionsAddEquiv J U F).symm x) +
        sectionsAddEquiv J T F (b ≫ (sectionsAddEquiv J U F).symm x)
    rw [Preadditive.add_comp, map_add]

/-- Composition of original free arrows acts by the original opposite composition. -/
theorem representedSectionsMap_comp {T U V : C}
    (a : freeAbelianSheaf.{t} J T ⟶ freeAbelianSheaf.{t} J U)
    (b : freeAbelianSheaf.{t} J U ⟶ freeAbelianSheaf.{t} J V) :
    representedSectionsMap J (a ≫ b) =
      representedSectionsMap J b ≫ representedSectionsMap J a := by
  ext F x
  change sectionsAddEquiv J T F ((a ≫ b) ≫ (sectionsAddEquiv J V F).symm x) =
    sectionsAddEquiv J T F (a ≫ (sectionsAddEquiv J U F).symm
      (sectionsAddEquiv J U F (b ≫ (sectionsAddEquiv J V F).symm x)))
  rw [AddEquiv.symm_apply_apply, Category.assoc]

/-- Finite sums retain the same original represented section transformations. -/
theorem representedSectionsMap_sum {T U : C} {I : Type i} (s : Finset I)
    (a : I → (freeAbelianSheaf.{t} J T ⟶ freeAbelianSheaf.{t} J U)) :
    representedSectionsMap J (∑ i ∈ s, a i) = ∑ i ∈ s, representedSectionsMap J (a i) :=
  map_sum (representedSectionsMapAddHom J) _ _

/-- The original local free-arrow relation is a whole natural transformation
identity on all coefficient sheaves. -/
theorem representedSectionsMap_local {T U V : C}
    (a : freeAbelianSheaf.{t} J T ⟶ freeAbelianSheaf.{t} J U)
    (p : V ⟶ T) {I : Type i} [Fintype I] (s : I → (V ⟶ U))
    (ha : (freeAbelianSheafFunctor.{t} J).map p ≫ a =
      ∑ i, (freeAbelianSheafFunctor.{t} J).map (s i)) :
    representedSectionsMap J a ≫ (sheafSections J AddCommGrpCat.{max h t}).map p.op =
      ∑ i, (sheafSections J AddCommGrpCat.{max h t}).map (s i).op := by
  have h := congrArg (representedSectionsMap J) ha
  simpa only [representedSectionsMap_comp, representedSectionsMap_sum,
    representedSectionsMap_freeMap] using h

end RepresentedSections

open CategoryTheory.MorphismProperty.Over

variable {C : Type c} [Category.{h} C] [HasPullbacks C]
  (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  {X : C} (J : GrothendieckTopology (P.Over ⊤ X))
  [HasSheafify J AddCommGrpCat.{max h t}]
  [∀ V : P.Over ⊤ X, (productTest P V).IsContinuous J J]
  (U : P.Over ⊤ X)
  (a : freeAbelianSheaf.{t} J (productTerminal P X) ⟶ freeAbelianSheaf.{t} J U)

/-- On a splitting chart, the entire represented restriction trace is the sum
of the original graph restrictions, naturally in every coefficient sheaf. -/
theorem representedRestrictionTrace_local (V : P.Over ⊤ X)
    {I : Type i} [Fintype I] (s : I → (V ⟶ U))
    (ha : (freeAbelianSheafFunctor.{t} J).map ((mkIdTerminal P X).from V) ≫ a =
      ∑ i, (freeAbelianSheafFunctor.{t} J).map (s i)) :
    Functor.whiskerRight (representedRestrictionTrace P J U a)
        ((sheafSections J AddCommGrpCat.{max h t}).obj (op V)) ≫
      (Functor.leftUnitor ((sheafSections J AddCommGrpCat.{max h t}).obj (op V))).hom =
      ∑ i, (sheafSections J AddCommGrpCat.{max h t}).map (productGraph P (s i)).op := by
  apply NatTrans.ext
  funext F
  have hl := NatTrans.congr_app
    (representedSectionsMap_local J a ((mkIdTerminal P X).from V) s ha)
      ((productSheaf P J V).obj F)
  simp only [NatTrans.comp_app, NatTrans.app_sum] at hl
  change (representedSectionsMap J a).app ((productSheaf P J V).obj F) ≫
      F.obj.map ((productTest P V).map ((mkIdTerminal P X).from V)).op =
    ∑ i, F.obj.map ((productTest P V).map (s i)).op at hl
  have ht := congrArg (fun g => F.obj.map g.op) (productGraph_terminal P V)
  rw [op_comp, F.obj.map_comp] at ht
  simp only [NatTrans.comp_app, NatTrans.app_sum]
  change F.obj.map (productSymmetry P V U).hom.op ≫
      (representedSectionsMap J a).app ((productSheaf P J V).obj F) ≫
        F.obj.map (productTerminalIso P V).inv.op =
    ∑ i, F.obj.map (productGraph P (s i)).op
  rw [← ht, ← Category.assoc _ _ (F.obj.map (productGraph P (𝟙 V)).op), hl,
    Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← F.obj.map_comp, ← op_comp, ← F.obj.map_comp, ← op_comp,
    Category.assoc, productGraph_diagonal_map_symmetry]

end CategoryTheory.Sheaf.Hypercohomology
