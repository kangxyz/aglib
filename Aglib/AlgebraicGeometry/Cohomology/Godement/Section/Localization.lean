/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Section.Units

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementClosedSectionSpanLocalization.lean` at
LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 132]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # Original localized maps of the closed-section Godement span -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The standard derived category of module sheaves used for the section/total comparison. -/
local instance sectionSpanLocalizationStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The original total comparison followed by the installed closed-section units. -/
def sectionTotalDerivedComparison {X Y : Scheme.{u}}
    (s : X ⟶ Y) (p : Y ⟶ X) (h : s ≫ p = 𝟙 X)
    (C : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.obj ((sectionTotalImage s p).obj C) ⟶
      DerivedCategory.Plus.Q.obj C :=
  (godementTotalDerivedPushforwardIso p).hom.app
      ((Scheme.Modules.pushforward s).mapCochainComplexPlus.obj C) ≫
    (derivedPushforwardPlus p).map ((derivedPushforwardPlusUnit s).app C) ≫
      (derivedPushforwardPlusSectionIso s p h).hom.app (DerivedCategory.Plus.Q.obj C)

/-- The installed section unit comparison before choosing a total representative. -/
def sectionDerivedUnitComparison {X Y : Scheme.{u}}
    (s : X ⟶ Y) (p : Y ⟶ X) (h : s ≫ p = 𝟙 X) :
    (Scheme.Modules.pushforward s).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus p ⟶ DerivedCategory.Plus.Q where
  app C := (derivedPushforwardPlus p).map ((derivedPushforwardPlusUnit s).app C) ≫
    (derivedPushforwardPlusSectionIso s p h).hom.app (DerivedCategory.Plus.Q.obj C)
  naturality {C D} f := by
    have hu := (derivedPushforwardPlusUnit s).naturality f
    have hs := (derivedPushforwardPlusSectionIso s p h).hom.naturality
      (DerivedCategory.Plus.Q.map f)
    dsimp only [Functor.comp_map, Functor.id_map] at hu hs ⊢
    have hup := (derivedPushforwardPlus p).congr_map hu
    simp only [Functor.map_comp] at hup
    rw [← Category.assoc, hup, Category.assoc, hs, Category.assoc]

/-- The actual total and installed section comparisons form a natural transformation. -/
def sectionTotalDerivedComparisonNat {X Y : Scheme.{u}}
    (s : X ⟶ Y) (p : Y ⟶ X) (h : s ≫ p = 𝟙 X) :
    sectionTotalImage s p ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q :=
  (associator (Scheme.Modules.pushforward s).mapCochainComplexPlus
      (godementTotalPlus Y ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus)
      DerivedCategory.Plus.Q).hom ≫
    whiskerLeft (Scheme.Modules.pushforward s).mapCochainComplexPlus
      (associator (godementTotalPlus Y)
        (Scheme.Modules.pushforward p).mapCochainComplexPlus DerivedCategory.Plus.Q).hom ≫
    whiskerLeft (Scheme.Modules.pushforward s).mapCochainComplexPlus
      (godementTotalDerivedPushforwardIso p).hom ≫ sectionDerivedUnitComparison s p h

/-- The natural comparison has exactly the original component formula. -/
lemma sectionTotalDerivedComparisonNat_app {X Y : Scheme.{u}}
    (s : X ⟶ Y) (p : Y ⟶ X) (h : s ≫ p = 𝟙 X)
    (C : CochainComplex.Plus X.Modules) :
    (sectionTotalDerivedComparisonNat s p h).app C =
      sectionTotalDerivedComparison s p h C := by
  simp only [sectionTotalDerivedComparisonNat, sectionDerivedUnitComparison,
    sectionTotalDerivedComparison, NatTrans.comp_app, whiskerLeft_app,
    associator_hom_app]
  erw [Category.id_comp, Category.id_comp]

/-- The first original span arrow retains naturality of all three installed comparisons. -/
lemma sectionTotalToRepeated_derivedComparison {X Y : Scheme.{u}}
    (s : X ⟶ Y) (p : Y ⟶ X) (h : s ≫ p = 𝟙 X)
    (C : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.map ((sectionTotalToRepeated s p).app C) ≫
      sectionTotalDerivedComparison s p h ((godementTotalPlus X).obj C) =
    sectionTotalDerivedComparison s p h C ≫
      DerivedCategory.Plus.Q.map ((godementTotalPlusUnit X).app C) := by
  have hn := (sectionTotalDerivedComparisonNat s p h).naturality
    ((godementTotalPlusUnit X).app C)
  simpa only [sectionTotalDerivedComparisonNat_app, Functor.comp_map,
    sectionTotalImage, sectionTotalToRepeated, Functor.id_obj, Functor.comp_obj] using hn

/-- The localized actual second span arrow, proved weak before localization. -/
def sectionSourceTotalToRepeatedDerivedIso {X Y : Scheme.{u}}
    (s : X ⟶ Y) (p : Y ⟶ X) (h : s ≫ p = 𝟙 X)
    (C : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.obj ((godementTotalPlus X).obj C) ≅
      DerivedCategory.Plus.Q.obj ((sectionRepeatedTotalImage s p).obj C) := by
  let : IsIso (DerivedCategory.Plus.Q.map ((sectionSourceTotalToRepeated s p h).app C)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso X.Modules) _
      (sectionSourceTotalToRepeated_quasiIso s p h C)
  exact asIso (DerivedCategory.Plus.Q.map ((sectionSourceTotalToRepeated s p h).app C))

/-- The localized actual source augmentation. -/
def sourceTotalAugmentationDerivedIso (X : Scheme.{u})
    (C : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.obj C ≅
      DerivedCategory.Plus.Q.obj ((godementTotalPlus X).obj C) := by
  let : IsIso (DerivedCategory.Plus.Q.map ((godementTotalPlusUnit X).app C)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso X.Modules) _
      (godementTotalPlusUnit_quasiIso X C)
  exact asIso (DerivedCategory.Plus.Q.map ((godementTotalPlusUnit X).app C))

/-- The prescribed weak span recovers the actual installed derived section comparison. -/
lemma sectionTotalToRepeated_localized {X Y : Scheme.{u}}
    (s : X ⟶ Y) (p : Y ⟶ X) (h : s ≫ p = 𝟙 X)
    (C : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.map ((sectionTotalToRepeated s p).app C) ≫
      (sectionSourceTotalToRepeatedDerivedIso s p h C).inv ≫
        (sourceTotalAugmentationDerivedIso X C).inv =
      sectionTotalDerivedComparison s p h C := by
  have hb : (sectionSourceTotalToRepeatedDerivedIso s p h C).hom ≫
      sectionTotalDerivedComparison s p h ((godementTotalPlus X).obj C) = 𝟙 _ :=
    sectionSourceTotalToRepeated_derivedUnit s p h C
  have hd : sectionTotalDerivedComparison s p h ((godementTotalPlus X).obj C) =
      (sectionSourceTotalToRepeatedDerivedIso s p h C).inv := by
    apply (cancel_epi (sectionSourceTotalToRepeatedDerivedIso s p h C).hom).mp
    rw [Iso.hom_inv_id]
    exact hb
  have ha := sectionTotalToRepeated_derivedComparison s p h C
  rw [hd] at ha
  rw [← Category.assoc, ha, Category.assoc]
  change sectionTotalDerivedComparison s p h C ≫
    ((sourceTotalAugmentationDerivedIso X C).hom ≫
      (sourceTotalAugmentationDerivedIso X C).inv) = _
  rw [Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules.Godement
