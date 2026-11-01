/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Hypercohomology.ContinuousPullbackConstant

/-! # Native terminal transport for constant inverse-image sources

Evaluation at the image terminal object is transported to the chosen terminal
object using its actual unique isomorphism. The original constant adjunction
unit is preserved; no new constant comparison is postulated.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.Hypercohomology

section Terminal

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (A : Type*) [Category* A] [HasSheafify J A]
  {T V : C} (hT : IsTerminal T) (hV : IsTerminal V)

/-- The actual section transport between two terminal objects. -/
def terminalSectionsIso :
    (sheafSections J A).obj (op T) ≅ (sheafSections J A).obj (op V) :=
  NatIso.ofComponents (fun F => F.obj.mapIso (hT.uniqueUpToIso hV).symm.op)
    (fun f => (f.hom.naturality (hT.uniqueUpToIso hV).inv.op).symm)

/-- Constant-adjunction units respect the actual terminal section transport. -/
theorem constantSheafAdj_terminalSectionsIso_unit (M : A) :
    (constantSheafAdj J A hT).unit.app M ≫
      (terminalSectionsIso J A hT hV).hom.app ((constantSheaf J A).obj M) =
    (constantSheafAdj J A hV).unit.app M := by
  simp only [constantSheafAdj, Adjunction.comp_unit_app]
  change (𝟙 M ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T)) ≫
    (sheafify J ((Functor.const Cᵒᵖ).obj M)).map (hT.uniqueUpToIso hV).inv.op =
    𝟙 M ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op V)
  simp only [Category.id_comp]
  exact ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).naturality
    (hT.uniqueUpToIso hV).inv.op).symm.trans (Category.id_comp _)

/-- Transporting the original constant adjunction changes only its terminal
section realization, not its unit or constant sheaf functor. -/
theorem constantSheafAdj_ofNatIsoRight_terminalSectionsIso :
    (constantSheafAdj J A hT).ofNatIsoRight (terminalSectionsIso J A hT hV) =
      constantSheafAdj J A hV := by
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  exact constantSheafAdj_terminalSectionsIso_unit J A hT hV M

end Terminal

section Pullback

universe c h d k v

variable {C : Type c} [Category.{h} C] {D : Type d} [Category.{k} D]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{max h k v}]
  [HasSheafify K AddCommGrpCat.{max h k v}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h k v} J K).IsRightAdjoint]
  (U : C) (hU : IsTerminal U) (hGU : IsTerminal (G.obj U))
  (V : D) (hV : IsTerminal V)

/-- Actual direct image followed by terminal evaluation, at the chosen target
terminal object rather than merely at the image object. -/
def continuousDirectImageTerminalSectionsIso :
    G.sheafPushforwardContinuous AddCommGrpCat.{max h k v} J K ⋙
      (sheafSections J AddCommGrpCat.{max h k v}).obj (op U) ≅
    (sheafSections K AddCommGrpCat.{max h k v}).obj (op V) :=
  continuousDirectImageSectionsIso G J K U ≪≫
    terminalSectionsIso K AddCommGrpCat.{max h k v} hGU hV

/-- The original constant-integer comparison equals the native comparison at
any chosen target terminal object, with its actual terminal transport. -/
theorem pullbackConstantIntegerIso_hom_eq_terminalComparison :
    (pullbackConstantIntegerIso.{c, h, d, k, v} G J K U hU hGU).hom =
      ((((constantSheafAdj J AddCommGrpCat.{max h k v} hU).comp
        (G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K)).ofNatIsoRight
          (continuousDirectImageTerminalSectionsIso G J K U hGU V hV)).leftAdjointUniq
        (constantSheafAdj K AddCommGrpCat.{max h k v} hV)).hom.app
          (AddCommGrpCat.of (ULift.{max h k v} ℤ)) := by
  rw [pullbackConstantIntegerIso_hom_eq_leftAdjointUniq]
  let a := (constantSheafAdj J AddCommGrpCat.{max h k v} hU).comp
    (G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K)
  let b := constantSheafAdj K AddCommGrpCat.{max h k v} hGU
  let e := continuousDirectImageSectionsIso G J K U
  let d := terminalSectionsIso K AddCommGrpCat.{max h k v} hGU hV
  let Z := AddCommGrpCat.of (ULift.{max h k v} ℤ)
  have he := Adjunction.homEquiv_leftAdjointUniq_hom_app (a.ofNatIsoRight e) b Z
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at he
  change ((a.ofNatIsoRight e).leftAdjointUniq b).hom.app Z =
    ((a.ofNatIsoRight (e ≪≫ d)).leftAdjointUniq
      (constantSheafAdj K AddCommGrpCat.{max h k v} hV)).hom.app Z
  apply ((a.ofNatIsoRight (e ≪≫ d)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply]
  change a.homEquiv _ _ (((a.ofNatIsoRight e).leftAdjointUniq b).hom.app Z) ≫
    (e.hom.app _ ≫ d.hom.app _) = _
  rw [← Category.assoc, he]
  exact constantSheafAdj_terminalSectionsIso_unit K AddCommGrpCat.{max h k v} hGU hV Z

end Pullback

end CategoryTheory.Sheaf.Hypercohomology
