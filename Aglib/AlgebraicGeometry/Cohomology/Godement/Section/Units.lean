/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Section.Span

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementClosedSectionSpanUnits.lean` at LOCAL
Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 92]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # Original installed units of the closed-section Godement span -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The standard derived-category model for module sheaves on `X` in section-unit comparisons. -/
local instance sectionSpanUnitsStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The original pushed augmentation followed by the actual total comparison is the installed unit.
-/
lemma pushedUnit_totalDerivedComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.map ((Scheme.Modules.pushforward f).mapCochainComplexPlus.map
        ((godementTotalPlusUnit X).app J)) ≫
      (godementTotalDerivedPushforwardIso f).hom.app J =
        (derivedPushforwardPlusUnit f).app J := by
  have hn := (derivedPushforwardPlusUnit f).naturality ((godementTotalPlusUnit X).app J)
  dsimp only [Functor.comp_map] at hn
  change DerivedCategory.Plus.Q.map
      ((Scheme.Modules.pushforward f).mapCochainComplexPlus.map
        ((godementTotalPlusUnit X).app J)) ≫
    ((derivedPushforwardPlusUnit f).app ((godementTotalPlus X).obj J) ≫
      (asIso (godementTotalDerivedAugmentation f)).inv.app J) = _
  rw [← Category.assoc, hn, Category.assoc]
  change (derivedPushforwardPlusUnit f).app J ≫
    ((asIso (godementTotalDerivedAugmentation f)).hom.app J ≫
      (asIso (godementTotalDerivedAugmentation f)).inv.app J) = _
  rw [Iso.hom_inv_id_app, Category.comp_id]

/-- The original complex section comparison retains both installed derived units. -/
lemma sectionComplexPlusIso_derivedUnit {X Y : Scheme.{u}}
    (s : X ⟶ Y) (p : Y ⟶ X) (h : s ≫ p = 𝟙 X)
    (C : CochainComplex.Plus X.Modules) :
    (derivedPushforwardPlusUnit p).app
        ((Scheme.Modules.pushforward s).mapCochainComplexPlus.obj C) ≫
      (derivedPushforwardPlus p).map ((derivedPushforwardPlusUnit s).app C) ≫
        (derivedPushforwardPlusSectionIso s p h).hom.app (DerivedCategory.Plus.Q.obj C) =
      DerivedCategory.Plus.Q.map ((sectionComplexPlusIso s p h).hom.app C) := by
  have ht := derivedPushforwardPlusSectionIso_unit s p h C
  rw [Functor.rightDerivedFunctorPlusCompUnit_app] at ht
  rw [Category.assoc] at ht
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.mapHomologicalComplex,
    Functor.mapCochainComplexPlus, ObjectProperty.lift,
    CochainComplex.Plus.ι, ObjectProperty.ι, inducedFunctor] at ht ⊢
  simp only [sectionComplexPlusIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.mapCochainComplexPlusCompIso, NatIso.ofComponents_inv_app, Iso.refl_inv,
    derivedPushforwardPlus, derivedPushforwardPlusUnit] at ⊢
  erw [Category.id_comp]
  exact ht

/-- The exact original section inverse and pushed flasque unit retain the installed section law. -/
lemma sectionSourceTotalToRepeated_derivedUnit {X Y : Scheme.{u}}
    (s : X ⟶ Y) (p : Y ⟶ X) (h : s ≫ p = 𝟙 X)
    (C : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.map ((sectionSourceTotalToRepeated s p h).app C) ≫
      (godementTotalDerivedPushforwardIso p).hom.app
        ((Scheme.Modules.pushforward s).mapCochainComplexPlus.obj ((godementTotalPlus X).obj C)) ≫
      (derivedPushforwardPlus p).map
        ((derivedPushforwardPlusUnit s).app ((godementTotalPlus X).obj C)) ≫
      (derivedPushforwardPlusSectionIso s p h).hom.app
        (DerivedCategory.Plus.Q.obj ((godementTotalPlus X).obj C)) =
      𝟙 (DerivedCategory.Plus.Q.obj ((godementTotalPlus X).obj C)) := by
  let T := (godementTotalPlus X).obj C
  let J := (Scheme.Modules.pushforward s).mapCochainComplexPlus.obj T
  have hg := congrArg (fun q => q ≫ (derivedPushforwardPlus p).map
    ((derivedPushforwardPlusUnit s).app T) ≫
      (derivedPushforwardPlusSectionIso s p h).hom.app (DerivedCategory.Plus.Q.obj T))
    (pushedUnit_totalDerivedComparison p J)
  simp only [Category.assoc] at hg
  dsimp only [sectionSourceTotalToRepeated]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [hg, sectionComplexPlusIso_derivedUnit s p h T]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  simpa only [Functor.id_obj] using
    (DerivedCategory.Plus.Q).map_id ((godementTotalPlus X).obj C)

end AlgebraicGeometry.Scheme.Modules.Godement
