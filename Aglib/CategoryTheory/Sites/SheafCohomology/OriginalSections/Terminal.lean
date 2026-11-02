/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.Pullback
public import Aglib.CategoryTheory.Sites.Hypercohomology.Terminal
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Naturality
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Continuous

/-! # Actual terminal sections and original constant sources

The actual site functors, original adjunctions and terminal-object transports
construct the whole section comparisons. Constant-source coherence is proved
from the same adjunction units and sheafification unit, before deriving any
cohomological map. The represented integer augmentation retains its literal
free representable and original constant/free-terminal isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.OriginalSections

universe uC vC uD vD uE vE uA vA t

section Sections

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type uA) [Category.{vA} A] (Q : C ⥤ D) [Q.IsContinuous J K]
  {T : C} {S : D} (τ : Q.obj T ≅ S)

/-- The original section comparison is contravariant terminal transport. -/
def terminalSectionsIso :
    Q.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj (op T) ≅
      (sheafSections K A).obj (op S) :=
  NatIso.ofComponents (fun F => F.obj.mapIso τ.symm.op)
    (fun q => (q.hom.naturality τ.inv.op).symm)

end Sections

section Composition

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (M : GrothendieckTopology E)
  (A : Type uA) [Category.{vA} A]
  (Q₁ : C ⥤ D) (Q₂ : D ⥤ E) (Q₀ : C ⥤ E)
  [Q₁.IsContinuous J K] [Q₂.IsContinuous K M] [Q₀.IsContinuous J M]
  (c : Q₀ ≅ Q₁ ⋙ Q₂) {T : C} {S : D} {V : E}
  (τ₁ : Q₁.obj T ≅ S) (τ₂ : Q₂.obj S ≅ V) (τ₀ : Q₀.obj T ≅ V)
  (hV : IsTerminal V)

include hV in
/-- The whole section composition law follows from uniqueness into the original terminal object. -/
theorem terminalSectionsIso_comp :
    Functor.isoWhiskerLeft (Q₂.sheafPushforwardContinuous A K M)
        (terminalSectionsIso J K A Q₁ τ₁) ≪≫ terminalSectionsIso K M A Q₂ τ₂ =
      (Functor.associator (Q₂.sheafPushforwardContinuous A K M)
        (Q₁.sheafPushforwardContinuous A J K) ((sheafSections J A).obj (op T))).symm ≪≫
        Functor.isoWhiskerRight (Functor.sheafPushforwardContinuousComp' c.symm A J K M)
          ((sheafSections J A).obj (op T)) ≪≫ terminalSectionsIso J M A Q₀ τ₀ := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  have hraw : F.obj.map (Q₂.map τ₁.inv).op ≫ F.obj.map τ₂.inv.op =
      F.obj.map (c.hom.app T).op ≫ F.obj.map τ₀.inv.op := by
    rw [← F.obj.map_comp, ← F.obj.map_comp]
    apply congrArg F.obj.map
    exact congrArg Quiver.Hom.op
      ((hV.ofIso ((Q₂.mapIso τ₁) ≪≫ τ₂).symm).hom_ext _ _)
  dsimp only [terminalSectionsIso, Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuous,
    Iso.trans_hom, Iso.symm_hom, NatIso.ofComponents_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.mapIso_hom, Iso.op, Functor.op, NatTrans.op,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj, sheafSections]
  dsimp only [ObjectProperty.lift, Functor.whiskeringLeft, sheafToPresheaf,
    ObjectProperty.ι, inducedFunctor, Functor.flip, Iso.refl,
    Functor.comp_map, Functor.comp_obj, NatTrans.id_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.comp_app, Functor.whiskerRight_app]
  simpa only [Category.id_comp, Quiver.Hom.unop_op, Iso.symm_inv] using hraw

end Composition

section Constant

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type uA) [Category.{vA} A]
  [HasSheafify J A] [HasSheafify K A]
  (Q : C ⥤ D) [Q.IsContinuous J K]
  {T : C} (hT : IsTerminal T) {S : D} (hS : IsTerminal S)
  (hQT : IsTerminal (Q.obj T))
  (F : Sheaf J A ⥤ Sheaf K A) (adj : F ⊣ Q.sheafPushforwardContinuous A J K)

/-- The fixed-terminal mate is the original constant comparison at the transported terminal. -/
theorem terminalConstantCanonical_eq :
    Adjunction.leftAdjointCompIso (constantSheafAdj J A hT) adj
        (constantSheafAdj K A hS)
        (terminalSectionsIso J K A Q (hQT.uniqueUpToIso hS)) =
      ((constantSheafAdj J A hT).comp adj).leftAdjointUniq
        (constantSheafAdj K A hQT) := by
  apply Iso.ext
  apply NatTrans.ext
  funext B
  let cAdj := constantSheafAdj J A hT
  let targetAdj := constantSheafAdj K A hQT
  let τ := hQT.uniqueUpToIso hS
  apply ((cAdj.comp adj).homEquiv _ _).injective
  refine Eq.trans (unit_conjugateEquiv_symm (constantSheafAdj K A hS)
    (cAdj.comp adj) (terminalSectionsIso J K A Q τ).inv B).symm ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app
    (cAdj.comp adj) targetAdj B).symm
  dsimp only [targetAdj]
  simp only [constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, Category.id_comp]
  change (toSheafify K ((Functor.const Dᵒᵖ).obj B)).app (op S) ≫
      (sheafify K ((Functor.const Dᵒᵖ).obj B)).map τ.hom.op =
    (toSheafify K ((Functor.const Dᵒᵖ).obj B)).app (op (Q.obj T))
  exact ((toSheafify K ((Functor.const Dᵒᵖ).obj B)).naturality τ.hom.op).symm.trans
    (Category.id_comp _)

end Constant

section Identity

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  (A : Type uA) [Category.{vA} A] [HasSheafify J A]
  (Q : C ⥤ C) [Q.IsContinuous J J] (c : Q ≅ 𝟭 C)
  (F : Sheaf J A ⥤ Sheaf J A) (adj : F ⊣ Q.sheafPushforwardContinuous A J J)

omit [HasSheafify J A] in
/-- The original left identity comparison is obtained from the actual right comparison. -/
def sheafLeftIdentityIso : F ≅ 𝟭 (Sheaf J A) :=
  (adj.ofNatIsoRight (Functor.sheafPushforwardContinuousId' c A J)).leftAdjointUniq
    Adjunction.id

/-- The original left identity comparison agrees with the original constant source map. -/
theorem sheafLeftIdentityIso_constant {T : C} (hT : IsTerminal T)
    (hQT : IsTerminal (Q.obj T)) (B : A) :
    (sheafLeftIdentityIso J A Q c F adj).hom.app ((constantSheaf J A).obj B) =
      (((constantSheafAdj J A hT).comp adj).leftAdjointUniq
        (constantSheafAdj J A hQT)).hom.app B := by
  let cAdj := constantSheafAdj J A hT
  let e := Functor.sheafPushforwardContinuousId' c A J
  apply ((cAdj.comp adj).homEquiv _ _).injective
  refine Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app
    (cAdj.comp adj) (constantSheafAdj J A hQT) B).symm
  rw [Adjunction.comp_homEquiv]
  dsimp only [Functor.id_obj]
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj.ofNatIsoRight e) (Adjunction.id (C := Sheaf J A)) ((constantSheaf J A).obj B)
  simp only [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have h' : adj.homEquiv _ _
      ((sheafLeftIdentityIso J A Q c F adj).hom.app ((constantSheaf J A).obj B)) =
      e.inv.app _ := by
    apply (cancel_mono (e.hom.app _)).mp
    exact h.trans (e.inv_hom_id_app _).symm
  refine (congrArg (cAdj.homEquiv B _) h').trans ?_
  dsimp only [cAdj, e]
  rw [Adjunction.homEquiv_unit]
  simp only [constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, Category.id_comp]
  change (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op T) ≫
      (𝟙 _ ≫ (sheafify J ((Functor.const Cᵒᵖ).obj B)).map (c.hom.app T).op) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op (Q.obj T))
  rw [Category.id_comp]
  exact ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).naturality (c.hom.app T).op).symm.trans
    (Category.id_comp _)

end Identity

section IntegerAugmentation

open Hypercohomology SliceCohomology

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max vC t}] {T : C} (hT : IsTerminal T)

/-- The original represented integer augmentation, through the original terminal source. -/
def representedIntegerAugmentation (U : C) :
    freeAbelianSheaf.{t} J U ⟶
      (constantSheaf J AddCommGrpCat.{max vC t}).obj
        (AddCommGrpCat.of (ULift.{max vC t} ℤ)) :=
  (freeAbelianSheafFunctor.{t} J).map (hT.from U) ≫
    (constantIntegerFreeTerminalIso J hT).inv

/-- The original augmentation restricts the original integer-one section. -/
theorem representedIntegerAugmentation_sections (U : C)
    (F : Sheaf J AddCommGrpCat.{max vC t})
    (a : (constantSheaf J AddCommGrpCat.{max vC t}).obj
      (AddCommGrpCat.of (ULift.{max vC t} ℤ)) ⟶ F) :
    sectionsEquiv.{t} J U F (representedIntegerAugmentation J hT U ≫ a) =
      F.obj.map (hT.from U).op (ModuleCoefficients.constantHomSectionsEquiv hT F a) := by
  dsimp only [representedIntegerAugmentation]
  rw [Category.assoc]
  have hpre := freeSections_naturality.{t} J (hT.from U) F
    ((constantIntegerFreeTerminalIso J hT).inv ≫ a)
  have h := constantIntegerFreeTerminalIso_evaluation J hT F
    ((constantIntegerFreeTerminalIso J hT).inv ≫ a)
  simp only [Iso.hom_inv_id_assoc] at h
  exact hpre.trans (congrArg (F.obj.map (hT.from U).op) h.symm)

end IntegerAugmentation

end CategoryTheory.Sheaf.OriginalSections
