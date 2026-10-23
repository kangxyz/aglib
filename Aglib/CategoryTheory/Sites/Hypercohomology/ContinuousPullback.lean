/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Hypercohomology.Terminal
public import Mathlib.CategoryTheory.Sites.Pullback

/-! # Original free and integer sources under continuous inverse image

The native inverse image carries an original free representable to the free
representable of the image object. The isomorphism is normalized by the actual
section adjunction. At terminal objects it identifies the original constant
integer sources used by sheaf cohomology.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

universe c h c' h' t

namespace CategoryTheory.Sheaf.Hypercohomology

variable {C : Type c} [Category.{h} C] {D : Type c'} [Category.{h'} D]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{max h h' t}]
  [HasSheafify K AddCommGrpCat.{max h h' t}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h h' t} J K).IsRightAdjoint]
  (U : C)

/-- The native inverse-image adjunction followed by original section evaluation. -/
def pullbackFreeSectionsEquiv (F : Sheaf K AddCommGrpCat.{max h h' t}) :
    ((G.sheafPullback AddCommGrpCat J K).obj (freeAbelianSheaf.{max h' t} J U) ⟶ F) ≃
      F.obj.obj (op (G.obj U)) :=
  ((G.sheafAdjunctionContinuous AddCommGrpCat J K).homEquiv _ F).trans
    (sectionsEquiv.{max h' t} J U ((G.sheafPushforwardContinuous AddCommGrpCat J K).obj F))

omit [HasSheafify K AddCommGrpCat.{max h h' t}] in
/-- The evaluation retains the original coefficient arrows. -/
theorem pullbackFreeSectionsEquiv_naturality
    {F F' : Sheaf K AddCommGrpCat.{max h h' t}}
    (a : (G.sheafPullback AddCommGrpCat J K).obj
      (freeAbelianSheaf.{max h' t} J U) ⟶ F) (f : F ⟶ F') :
    pullbackFreeSectionsEquiv G J K U F' (a ≫ f) =
      f.hom.app (op (G.obj U)) (pullbackFreeSectionsEquiv G J K U F a) := by
  dsimp only [pullbackFreeSectionsEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The actual continuous inverse image preserves original free representables. -/
def pullbackFreeAbelianSheafIso :
    (G.sheafPullback AddCommGrpCat J K).obj (freeAbelianSheaf.{max h' t} J U) ≅
      freeAbelianSheaf.{max h t} K (G.obj U) := by
  let E := ((sheafSections K AddCommGrpCat.{max h h' t}).obj (op (G.obj U))) ⋙
    forget AddCommGrpCat.{max h h' t}
  let a : E.CorepresentableBy
      ((G.sheafPullback AddCommGrpCat J K).obj (freeAbelianSheaf.{max h' t} J U)) :=
    { homEquiv := pullbackFreeSectionsEquiv G J K U _
      homEquiv_comp f x := pullbackFreeSectionsEquiv_naturality G J K U x f }
  let b : E.CorepresentableBy (freeAbelianSheaf.{max h t} K (G.obj U)) :=
    { homEquiv := sectionsEquiv.{max h t} K (G.obj U) _
      homEquiv_comp f x := sectionsEquiv_naturality.{max h t} K (G.obj U) x f }
  exact a.uniqueUpToIso b

/-- The source isomorphism preserves the actual section represented by an arrow. -/
theorem pullbackFreeAbelianSheafIso_evaluation
    (F : Sheaf K AddCommGrpCat.{max h h' t})
    (a : freeAbelianSheaf.{max h t} K (G.obj U) ⟶ F) :
    pullbackFreeSectionsEquiv G J K U F
      ((pullbackFreeAbelianSheafIso G J K U).hom ≫ a) =
        sectionsEquiv.{max h t} K (G.obj U) F a := by
  rw [pullbackFreeSectionsEquiv_naturality]
  change a.hom.app (op (G.obj U))
    (pullbackFreeSectionsEquiv G J K U _
      ((pullbackFreeSectionsEquiv G J K U _).symm
        (sectionsEquiv.{max h t} K (G.obj U) _ (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply]
  simpa only [Category.id_comp] using (sectionsEquiv_naturality.{max h t} K (G.obj U) (𝟙 _) a).symm

/-- At terminal objects, inverse image preserves the original constant integer
source, through the normalized original free-representable comparisons. -/
def pullbackConstantIntegerIso (hU : IsTerminal U) (hGU : IsTerminal (G.obj U)) :
    (G.sheafPullback AddCommGrpCat J K).obj
      ((constantSheaf J AddCommGrpCat.{max h h' t}).obj
        (AddCommGrpCat.of (ULift.{max h h' t} ℤ))) ≅
      (constantSheaf K AddCommGrpCat.{max h h' t}).obj
        (AddCommGrpCat.of (ULift.{max h h' t} ℤ)) :=
  (G.sheafPullback AddCommGrpCat J K).mapIso
      (constantIntegerFreeTerminalIso J hU) ≪≫
    pullbackFreeAbelianSheafIso G J K U ≪≫
    (constantIntegerFreeTerminalIso K hGU).symm

end CategoryTheory.Sheaf.Hypercohomology
