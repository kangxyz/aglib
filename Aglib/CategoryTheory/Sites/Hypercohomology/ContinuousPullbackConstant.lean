/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Hypercohomology.ContinuousPullback
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Original constant sources under continuous inverse image

The free-representable construction of the original constant-integer comparison
agrees with native constant-adjunction uniqueness. Both are normalized on the
actual terminal section; no replacement cohomology or source is chosen.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.Hypercohomology

open ModuleCoefficients

universe c h d k v

variable {C : Type c} [Category.{h} C] {D : Type d} [Category.{k} D]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{max h k v}]
  [HasSheafify K AddCommGrpCat.{max h k v}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h k v} J K).IsRightAdjoint]
  (U : C) (hU : IsTerminal U) (hGU : IsTerminal (G.obj U))

/-- Continuous direct image preserves evaluation at the actual image object. -/
def continuousDirectImageSectionsIso :
    G.sheafPushforwardContinuous AddCommGrpCat.{max h k v} J K ⋙
      (sheafSections J AddCommGrpCat.{max h k v}).obj (op U) ≅
    (sheafSections K AddCommGrpCat.{max h k v}).obj (op (G.obj U)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by rfl)

/-- The original inverse-image constant-integer comparison preserves the
actual terminal section, through its native adjunction. -/
theorem pullbackConstantIntegerIso_evaluation
    (F : Sheaf K AddCommGrpCat.{max h k v})
    (a : (constantSheaf K AddCommGrpCat.{max h k v}).obj
      (AddCommGrpCat.of (ULift.{max h k v} ℤ)) ⟶ F) :
    constantHomSectionsEquiv hU
      ((G.sheafPushforwardContinuous AddCommGrpCat.{max h k v} J K).obj F)
      ((G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K).homEquiv _ _
        ((pullbackConstantIntegerIso.{c, h, d, k, v} G J K U hU hGU).hom ≫ a)) =
      constantHomSectionsEquiv hGU F a := by
  change constantHomSectionsEquiv hU _
    ((G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K).homEquiv _ _
      ((G.sheafPullback AddCommGrpCat.{max h k v} J K).map
        (constantIntegerFreeTerminalIso.{c, h, max k v} J hU).hom ≫
        (pullbackFreeAbelianSheafIso.{c, h, d, k, v} G J K U).hom ≫
        (constantIntegerFreeTerminalIso.{d, k, max h v} K hGU).inv ≫ a)) = _
  rw [Adjunction.homEquiv_naturality_left,
    constantIntegerFreeTerminalIso_evaluation.{c, h, max k v}]
  change pullbackFreeSectionsEquiv.{c, h, d, k, v} G J K U F
    ((pullbackFreeAbelianSheafIso.{c, h, d, k, v} G J K U).hom ≫
      (constantIntegerFreeTerminalIso.{d, k, max h v} K hGU).inv ≫ a) = _
  rw [pullbackFreeAbelianSheafIso_evaluation]
  simpa only [Iso.hom_inv_id_assoc] using
    (constantIntegerFreeTerminalIso_evaluation.{d, k, max h v} K hGU F
      ((constantIntegerFreeTerminalIso.{d, k, max h v} K hGU).inv ≫ a)).symm

/-- The original integer-source comparison is precisely the component of the
native constant-adjunction comparison. -/
theorem pullbackConstantIntegerIso_hom_eq_leftAdjointUniq :
    (pullbackConstantIntegerIso.{c, h, d, k, v} G J K U hU hGU).hom =
      ((((constantSheafAdj J AddCommGrpCat.{max h k v} hU).comp
        (G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K)).ofNatIsoRight
          (continuousDirectImageSectionsIso G J K U)).leftAdjointUniq
        (constantSheafAdj K AddCommGrpCat.{max h k v} hGU)).hom.app
          (AddCommGrpCat.of (ULift.{max h k v} ℤ)) := by
  let Z := AddCommGrpCat.of (ULift.{max h k v} ℤ)
  let F := (constantSheaf K AddCommGrpCat.{max h k v}).obj Z
  apply ((G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K).homEquiv _ _).injective
  apply (constantHomSectionsEquiv hU _).injective
  have hq := pullbackConstantIntegerIso_evaluation G J K U hU hGU F (𝟙 F)
  have hid := congrArg (fun a => constantHomSectionsEquiv hU _
    ((G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K).homEquiv _ _ a))
    (Category.comp_id (pullbackConstantIntegerIso.{c, h, d, k, v} G J K U hU hGU).hom)
  rw [hid.symm.trans hq]
  have he := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj J AddCommGrpCat.{max h k v} hU).comp
      (G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K)).ofNatIsoRight
        (continuousDirectImageSectionsIso G J K U))
    (constantSheafAdj K AddCommGrpCat.{max h k v} hGU) Z
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at he
  let σ := (((constantSheafAdj J AddCommGrpCat.{max h k v} hU).comp
    (G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K)).ofNatIsoRight
      (continuousDirectImageSectionsIso G J K U)).leftAdjointUniq
        (constantSheafAdj K AddCommGrpCat.{max h k v} hGU)
  change (constantSheafAdj J AddCommGrpCat.{max h k v} hU).homEquiv _ _
    ((G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K).homEquiv _ _
      (σ.hom.app Z)) ≫ 𝟙 _ = _ at he
  rw [Category.comp_id] at he
  have hi : (constantSheafAdj K AddCommGrpCat.{max h k v} hGU).homEquiv Z F
      (𝟙 F) = (constantSheafAdj K AddCommGrpCat.{max h k v} hGU).unit.app Z := by
    rw [Adjunction.homEquiv_unit, Functor.map_id]
    exact Category.comp_id _
  change AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj.obj (op (G.obj U)))
      ((constantSheafAdj K AddCommGrpCat.{max h k v} hGU).homEquiv Z F (𝟙 F)) =
    AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj.obj (op (G.obj U)))
      ((constantSheafAdj J AddCommGrpCat.{max h k v} hU).homEquiv _ _
        ((G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K).homEquiv _ _
          (σ.hom.app Z)))
  rw [hi, he]

end CategoryTheory.Sheaf.Hypercohomology
