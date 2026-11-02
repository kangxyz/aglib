/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.Terminal
public import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Original inverse image, actual slice and integer source

The given actual site adjunction, its actual inverse-image adjunction and the
existing slice equivalence construct the comparison. Its original integer
source square is derived from their units and original terminal evaluations.
The original free representable and augmentation are retained throughout.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.Hypercohomology

namespace CategoryTheory.Sheaf.SliceCohomology

universe uC vC uD vD uA vA t

section Restriction

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type uA) [Category.{vA} A]
  {P : D ⥤ C} {Q : C ⥤ D} [P.IsContinuous K J] [Q.IsContinuous J K]
  (siteAdj : P ⊣ Q) {F : Sheaf J A ⥤ Sheaf K A}
  (imageAdj : F ⊣ Q.sheafPushforwardContinuous A J K)
  {T : C} (hT : IsTerminal T) {S : D} (τ : Q.obj T ≅ S)

/-- Actual ordinary section pullback becomes literal restriction
under the actual left uniqueness Iso. -/
theorem unitSections_restriction (L : Sheaf J A) :
    (Adjunction.unitSectionsNatTrans imageAdj ((sheafSections J A).obj (op T))
        (OriginalSections.terminalSectionsIso J K A Q τ)).app L ≫
      ((imageAdj.leftAdjointUniq
        (siteAdj.sheafPushforwardContinuous (E := A) K J)).hom.app L).hom.app (op S) =
    L.obj.map (hT.from (P.obj S)).op := by
  let adj := siteAdj.sheafPushforwardContinuous (E := A) K J
  have hu := Adjunction.unit_leftAdjointUniq_hom_app imageAdj adj L
  have h := congrArg
    (fun a : L ⟶ (Q.sheafPushforwardContinuous A J K).obj
        ((P.sheafPushforwardContinuous A K J).obj L) => a.hom.app (op T)) hu
  have hadj : (adj.unit.app L).hom.app (op T) =
      L.obj.map (siteAdj.counit.app T).op := by
    change 𝟙 _ ≫ L.obj.map (siteAdj.counit.app T).op ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  have hproj :
      (imageAdj.unit.app L ≫ (Q.sheafPushforwardContinuous A J K).map
        ((imageAdj.leftAdjointUniq adj).hom.app L)).hom.app (op T) =
      (imageAdj.unit.app L).hom.app (op T) ≫
        ((imageAdj.leftAdjointUniq adj).hom.app L).hom.app (op (Q.obj T)) := rfl
  have hraw := hproj.symm.trans (h.trans hadj)
  change ((imageAdj.unit.app L).hom.app (op T) ≫
      (F.obj L).obj.map τ.inv.op) ≫ _ = _
  rw [Category.assoc, ((imageAdj.leftAdjointUniq adj).hom.app L).hom.naturality,
    ← Category.assoc]
  refine (congrArg (fun k => k ≫
    ((P.sheafPushforwardContinuous A K J).obj L).obj.map τ.inv.op) hraw).trans ?_
  change L.obj.map (siteAdj.counit.app T).op ≫ L.obj.map (P.map τ.inv).op = _
  rw [← L.obj.map_comp, ← op_comp]
  congr 1
  congr 1
  exact hT.hom_ext _ _

end Restriction

section Slice

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C) (U : C)
  {D : Type uD} [Category.{vD} D] (K : GrothendieckTopology D) (E : Over U ≌ D)
  [E.inverse.IsDenseSubsite K (J.over U)]
  [HasSheafify J AddCommGrpCat.{max vC t}]
  [HasSheafify (J.over U) AddCommGrpCat.{max vC t}]
  [HasSheafify K AddCommGrpCat.{max vC t}]
  (hS : IsTerminal (E.functor.obj (Over.mk (𝟙 U))))

/-- The original constant comparison for the actual slice equivalence. -/
def originalSliceConstantIso :
    constantSheaf (J.over U) AddCommGrpCat.{max vC t} ⋙
        (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).functor ≅
      constantSheaf K AddCommGrpCat.{max vC t} :=
  ((constantSheafAdj (J.over U) AddCommGrpCat.{max vC t} Over.mkIdTerminal).comp
    (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).toAdjunction).leftAdjointUniq
      (constantSheafAdj K AddCommGrpCat.{max vC t} hS)

/-- The original equivalence-adjunction source map on the same integer object. -/
def originalSliceIntegerSource :
    sliceIntegers.{t} J U ⟶
      (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).inverse.obj
        ((constantSheaf K AddCommGrpCat.{max vC t}).obj
          (AddCommGrpCat.of (ULift.{max vC t} ℤ))) :=
  (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).unitIso.hom.app _ ≫
    (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).inverse.map
      ((originalSliceConstantIso J U K E hS).hom.app
        (AddCommGrpCat.of (ULift.{max vC t} ℤ)))

omit [HasSheafify J AddCommGrpCat.{max vC t}] in
/-- The actual equivalence source retains its original terminal integer-one evaluation. -/
theorem originalSliceIntegerSource_sections (L : Sheaf K AddCommGrpCat.{max vC t})
    (a : (constantSheaf K AddCommGrpCat.{max vC t}).obj
      (AddCommGrpCat.of (ULift.{max vC t} ℤ)) ⟶ L) :
    sliceSectionsAddEquiv.{t} J _
      (originalSliceIntegerSource J U K E hS ≫
        (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).inverse.map a) =
      ModuleCoefficients.constantHomSectionsEquiv hS L a := by
  let c := constantSheafAdj (J.over U) AddCommGrpCat.{max vC t} Over.mkIdTerminal
  let d := constantSheafAdj K AddCommGrpCat.{max vC t} hS
  let R := (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).inverse
  let e := (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).toAdjunction
  have h : (c.comp e).homEquiv _ L
      ((originalSliceConstantIso J U K E hS).hom.app
        (AddCommGrpCat.of (ULift.{max vC t} ℤ)) ≫ a) = d.homEquiv _ L a := by
    rw [Adjunction.homEquiv_naturality_right]
    change (c.comp e).homEquiv _ _ (((c.comp e).leftAdjointUniq d).hom.app _) ≫
      ((sheafSections K AddCommGrpCat.{max vC t}).obj
        (op (E.functor.obj (Over.mk (𝟙 U))))).map a = _
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact (Adjunction.homEquiv_unit d _ _ a).symm
  have h' := congrArg (fun k => k (ULift.up (1 : ℤ))) h
  change (c.homEquiv (AddCommGrpCat.of (ULift.{max vC t} ℤ)) (R.obj L)
    (originalSliceIntegerSource J U K E hS ≫ R.map a)) (ULift.up (1 : ℤ)) =
      (d.homEquiv _ L a) (ULift.up (1 : ℤ))
  refine Eq.trans ?_ h'
  have hq : originalSliceIntegerSource J U K E hS ≫ R.map a =
      e.homEquiv _ L ((originalSliceConstantIso J U K E hS).hom.app
        (AddCommGrpCat.of (ULift.{max vC t} ℤ)) ≫ a) := by
    change (e.unit.app _ ≫ R.map _) ≫ R.map a = e.unit.app _ ≫ R.map (_ ≫ a)
    exact (Category.assoc _ _ _).trans
      (congrArg (fun k => e.unit.app _ ≫ k) (R.map_comp _ a).symm)
  have hcomp := congrArg
    (fun k => (k (AddCommGrpCat.of (ULift.{max vC t} ℤ)) L
      ((originalSliceConstantIso J U K E hS).hom.app
        (AddCommGrpCat.of (ULift.{max vC t} ℤ)) ≫ a)) (ULift.up (1 : ℤ)))
    (Adjunction.comp_homEquiv c e)
  have heval := congrArg (fun k : sliceIntegers.{t} J U ⟶ R.obj L =>
    c.homEquiv (AddCommGrpCat.of (ULift.{max vC t} ℤ)) (R.obj L) k (ULift.up (1 : ℤ))) hq
  exact heval.trans hcomp.symm

end Slice

section OriginalSourceSquare

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C) (U : C)
  {D : Type uD} [Category.{vD} D] (K : GrothendieckTopology D) (E : Over U ≌ D)
  [E.inverse.IsDenseSubsite K (J.over U)]
  [HasSheafify J AddCommGrpCat.{max vC t}]
  [HasSheafify (J.over U) AddCommGrpCat.{max vC t}]
  [HasSheafify K AddCommGrpCat.{max vC t}]
  [(E.inverse ⋙ Over.forget U).IsContinuous K J]
  (Q : C ⥤ D) [Q.IsContinuous J K]
  (siteAdj : E.inverse ⋙ Over.forget U ⊣ Q)
  {F : Sheaf J AddCommGrpCat.{max vC t} ⥤ Sheaf K AddCommGrpCat.{max vC t}}
  (imageAdj : F ⊣ Q.sheafPushforwardContinuous AddCommGrpCat.{max vC t} J K)

/-- The existing slice equivalence followed by restriction is literal precomposition. -/
def originalSliceRestrictionIso :
    J.overPullback AddCommGrpCat.{max vC t} U ⋙
        (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).functor ≅
      (E.inverse ⋙ Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{max vC t} K J :=
  NatIso.ofComponents (fun L => ObjectProperty.isoMk _ (Iso.refl _)) (by
    intro L M q
    ext V a
    rfl)

/-- The actual inverse-image adjunction and actual site adjunction
construct the slice comparison. -/
def originalInverseImageSliceIso :
    F ≅ J.overPullback AddCommGrpCat.{max vC t} U ⋙
      (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).functor :=
  imageAdj.leftAdjointUniq
      (siteAdj.sheafPushforwardContinuous (E := AddCommGrpCat.{max vC t}) K J) ≪≫
    (originalSliceRestrictionIso J U K E).symm

/-- The original inverse image transported back through the same actual slice equivalence. -/
def originalInverseImageSliceInverseIso :
    F ⋙ (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).inverse ≅
      J.overPullback AddCommGrpCat.{max vC t} U :=
  Functor.isoWhiskerRight (originalInverseImageSliceIso J U K E Q siteAdj imageAdj)
      (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).inverse ≪≫
    Functor.isoWhiskerLeft (J.overPullback AddCommGrpCat.{max vC t} U)
      (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).unitIso.symm

variable {T : C} (hT : IsTerminal T)
  (hS : IsTerminal (E.functor.obj (Over.mk (𝟙 U))))
  (τ : Q.obj T ≅ E.functor.obj (Over.mk (𝟙 U)))
  (c : constantSheaf J AddCommGrpCat.{max vC t} ⋙ F ≅
    constantSheaf K AddCommGrpCat.{max vC t})
  (hc : c = Adjunction.leftAdjointCompIso (constantSheafAdj J AddCommGrpCat.{max vC t} hT)
    imageAdj (constantSheafAdj K AddCommGrpCat.{max vC t} hS)
    (OriginalSections.terminalSectionsIso J K AddCommGrpCat.{max vC t} Q τ))

include hc in
/-- The whole original integer-source square follows from the actual units and generator. -/
theorem originalInverseImageSlice_source_square :
    originalSliceIntegerSource J U K E hS ≫
        (E.sheafCongr (J.over U) K AddCommGrpCat.{max vC t}).inverse.map
          (c.inv.app (AddCommGrpCat.of (ULift.{max vC t} ℤ))) ≫
        (originalInverseImageSliceInverseIso J U K E Q siteAdj imageAdj).hom.app
          ((constantSheaf J AddCommGrpCat.{max vC t}).obj
            (AddCommGrpCat.of (ULift.{max vC t} ℤ))) =
      sliceComparisonUnit.{t} J U ≫
        (J.overPullback AddCommGrpCat.{max vC t} U).map
          (OriginalSections.representedIntegerAugmentation J hT U) := by
  let Z := (constantSheaf J AddCommGrpCat.{max vC t}).obj
    (AddCommGrpCat.of (ULift.{max vC t} ℤ))
  let z := ModuleCoefficients.constantHomSectionsEquiv hT Z (𝟙 Z)
  let β : U ⟶ (E.inverse ⋙ Over.forget U).obj (E.functor.obj (Over.mk (𝟙 U))) :=
    (E.unitIso.app (Over.mk (𝟙 U))).hom.left
  apply (sliceSectionsAddEquiv.{t} J _).injective
  rw [← Category.assoc, sliceSections_postcomp, originalSliceIntegerSource_sections,
    sliceSections_postcomp]
  have hgen : sliceSectionsAddEquiv.{t} J ((freeAbelianSheaf.{t} J U).over U)
      (sliceComparisonUnit.{t} J U) = sectionsAddEquiv.{t} J U (freeAbelianSheaf.{t} J U) (𝟙 _) :=
    sliceComparisonUnit_generator J U
  rw [hgen]
  have hcz := Adjunction.integerHomSectionsAddEquiv_pullback
    (constantSheafAdj J AddCommGrpCat.{max vC t} hT) imageAdj
    (constantSheafAdj K AddCommGrpCat.{max vC t} hS)
    (OriginalSections.terminalSectionsIso J K AddCommGrpCat.{max vC t} Q τ) c hc (𝟙 Z)
  have hFid : c.inv.app (AddCommGrpCat.of (ULift.{max vC t} ℤ)) ≫ F.map (𝟙 Z) =
      c.inv.app (AddCommGrpCat.of (ULift.{max vC t} ℤ)) :=
    (congrArg (fun q => c.inv.app (AddCommGrpCat.of (ULift.{max vC t} ℤ)) ≫ q)
      (F.map_id Z)).trans (Category.comp_id _)
  have hcz := (congrArg
    ((constantSheafAdj K AddCommGrpCat.{max vC t} hS).integerHomSectionsAddEquiv (F.obj Z))
      hFid).symm.trans hcz
  change ModuleCoefficients.constantHomSectionsEquiv hS (F.obj Z)
      (c.inv.app (AddCommGrpCat.of (ULift.{max vC t} ℤ))) =
    (Adjunction.unitSectionsNatTrans imageAdj
      ((sheafSections J AddCommGrpCat.{max vC t}).obj (op T))
      (OriginalSections.terminalSectionsIso J K AddCommGrpCat.{max vC t} Q τ)).app Z z at hcz
  refine (congrArg
    (((originalInverseImageSliceInverseIso J U K E Q siteAdj imageAdj).hom.app Z).hom.app
      (op (Over.mk (𝟙 U)))) hcz).trans ?_
  change Z.obj.map β.op
      (((imageAdj.leftAdjointUniq
        (siteAdj.sheafPushforwardContinuous (E := AddCommGrpCat.{max vC t}) K J)).hom.app Z).hom.app
          (op (E.functor.obj (Over.mk (𝟙 U))))
        ((Adjunction.unitSectionsNatTrans imageAdj
          ((sheafSections J AddCommGrpCat.{max vC t}).obj (op T))
          (OriginalSections.terminalSectionsIso J K AddCommGrpCat.{max vC t} Q τ)).app Z z)) =
    (OriginalSections.representedIntegerAugmentation J hT U).hom.app (op U)
      (sectionsEquiv.{t} J U (freeAbelianSheaf.{t} J U) (𝟙 _))
  have hg := congrArg (fun k => k z)
    (unitSections_restriction J K AddCommGrpCat.{max vC t} siteAdj imageAdj hT τ Z)
  refine (congrArg (Z.obj.map β.op) hg).trans ?_
  have ht : β ≫ hT.from ((E.inverse ⋙ Over.forget U).obj (E.functor.obj (Over.mk (𝟙 U)))) =
      hT.from U := hT.hom_ext _ _
  have hm := congrArg (fun k => k z) (Z.obj.map_comp
    (hT.from ((E.inverse ⋙ Over.forget U).obj (E.functor.obj (Over.mk (𝟙 U))))).op β.op)
  refine hm.symm.trans ?_
  refine (congrArg (fun k : U ⟶ T => Z.obj.map k.op z) ht).trans ?_
  let e : Z ≅ freeAbelianSheaf.{t} J T := constantIntegerFreeTerminalIso J hT
  have hz := constantIntegerFreeTerminalIso_evaluation J hT Z e.inv
  have hz' : z = sectionsEquiv.{t} J T Z e.inv :=
    (congrArg (ModuleCoefficients.constantHomSectionsEquiv hT Z) e.hom_inv_id).symm.trans hz
  have hpre := freeSections_naturality J (hT.from U) Z e.inv
  have hrep := sectionsEquiv_naturality J U (𝟙 (freeAbelianSheaf.{t} J U))
    (OriginalSections.representedIntegerAugmentation J hT U)
  have hid := congrArg (sectionsEquiv.{t} J U Z)
    (Category.id_comp (OriginalSections.representedIntegerAugmentation J hT U))
  exact (congrArg (Z.obj.map (hT.from U).op) hz').trans
    (hpre.symm.trans (hid.symm.trans hrep))

end OriginalSourceSquare

section TerminalAugmentation

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max vC t}] {T U : C} (hT : IsTerminal T)

/-- The original represented source at an isomorphic terminal test
is its original terminal transport. -/
theorem representedIntegerAugmentation_transport (τ : U ≅ T)
    (F : Sheaf J AddCommGrpCat.{max vC t})
    (a : (constantSheaf J AddCommGrpCat.{max vC t}).obj
      (AddCommGrpCat.of (ULift.{max vC t} ℤ)) ⟶ F) :
    sectionsEquiv.{t} J U F (OriginalSections.representedIntegerAugmentation J hT U ≫ a) =
      F.obj.map τ.hom.op (ModuleCoefficients.constantHomSectionsEquiv hT F a) := by
  rw [OriginalSections.representedIntegerAugmentation_sections]
  exact congrArg (fun k => F.obj.map k.op
    (ModuleCoefficients.constantHomSectionsEquiv hT F a)) (hT.hom_ext _ _)

end TerminalAugmentation

end CategoryTheory.Sheaf.SliceCohomology
