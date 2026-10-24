/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionCube
public import Mathlib.CategoryTheory.Whiskering

/-!
# Whole natural-isomorphism source cubes

The original composition and transport equations are retained as named propositions.
They imply equality of the two whole natural-isomorphism chains. Component evaluation
is a separate abstract theorem, so a concrete consumer need not expand native functor
projections while specializing the composition argument.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {L : A ⥤ B} {L' : C ⥤ D} {G : A ⥤ C} {H : B ⥤ D}
  {K : A' ⥤ B'} {K' : C' ⥤ D'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}

/-- The literal composition equation for three specified comparison isomorphisms. -/
def ComparisonCompositionEquation {T : A ⥤ D} {T' : A' ⥤ D'}
    (sL : L ⋙ QB ≅ QA ⋙ K) (sH : H ⋙ QD ≅ QB ⋙ H')
    (sT : T ⋙ QD ≅ QA ⋙ T') (c : T ≅ L ⋙ H) (d : T' ≅ K ⋙ H') : Prop :=
  ∀ X, d.hom.app (QA.obj X) ≫ H'.map (sL.inv.app X) ≫ sH.inv.app (L.obj X) =
    sT.inv.app X ≫ QD.map (c.hom.app X)

/-- The literal middle-transport equation for two specified comparisons. -/
def ComparisonTransportEquation {T₀ T₁ : A ⥤ D} {T₀' T₁' : A' ⥤ D'}
    (s₀ : T₀ ⋙ QD ≅ QA ⋙ T₀') (s₁ : T₁ ⋙ QD ≅ QA ⋙ T₁')
    (c : T₀ ≅ T₁) (d : T₀' ≅ T₁') : Prop :=
  ∀ X, d.hom.app (QA.obj X) ≫ s₁.inv.app X = s₀.inv.app X ≫ QD.map (c.hom.app X)

/-- Equality of the two original whole comparison chains around a source cube. -/
def ComparisonCubeEquation
    (sL : L ⋙ QB ≅ QA ⋙ K) (sL' : L' ⋙ QD ≅ QC ⋙ K')
    (sG : G ⋙ QC ≅ QA ⋙ G') (sH : H ⋙ QD ≅ QB ⋙ H')
    (sm : G ⋙ L' ≅ L ⋙ H) (sa : G' ⋙ K' ≅ K ⋙ H') : Prop :=
  isoWhiskerLeft QA sa ≪≫ (associator QA K H').symm ≪≫
      isoWhiskerRight sL.symm H' ≪≫ associator L QB H' ≪≫
      isoWhiskerLeft L sH.symm ≪≫ (associator L H QD).symm =
    (associator QA G' K').symm ≪≫ isoWhiskerRight sG.symm K' ≪≫
      associator G QC K' ≪≫ isoWhiskerLeft G sL'.symm ≪≫
      (associator G L' QD).symm ≪≫ isoWhiskerRight sm QD

/-- Evaluate the whole cube equality without expanding any specified comparison. -/
theorem comparisonCubeEquation_app
    (sL : L ⋙ QB ≅ QA ⋙ K) (sL' : L' ⋙ QD ≅ QC ⋙ K')
    (sG : G ⋙ QC ≅ QA ⋙ G') (sH : H ⋙ QD ≅ QB ⋙ H')
    (sm : G ⋙ L' ≅ L ⋙ H) (sa : G' ⋙ K' ≅ K ⋙ H')
    (h : ComparisonCubeEquation sL sL' sG sH sm sa) (X : A) :
    sa.hom.app (QA.obj X) ≫ H'.map (sL.inv.app X) ≫ sH.inv.app (L.obj X) =
      K'.map (sG.inv.app X) ≫ sL'.inv.app (G.obj X) ≫ QD.map (sm.hom.app X) := by
  have he := congrArg
    (fun e : QA ⋙ (G' ⋙ K') ≅ (L ⋙ H) ⋙ QD => e.hom.app X) h
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc] using he

variable {L₀ L₁ : A ⥤ D} {K₀ K₁ : A' ⥤ D'}

/-- Proved original composition and transport equations imply the whole source cube. -/
theorem comparisonCubeEquation_of_composition
    (sL : L ⋙ QB ≅ QA ⋙ K) (sL' : L' ⋙ QD ≅ QC ⋙ K')
    (sG : G ⋙ QC ≅ QA ⋙ G') (sH : H ⋙ QD ≅ QB ⋙ H')
    (s₀ : L₀ ⋙ QD ≅ QA ⋙ K₀) (s₁ : L₁ ⋙ QD ≅ QA ⋙ K₁)
    (c₀ : L₀ ≅ G ⋙ L') (c₁ : L₁ ≅ L ⋙ H) (c : L₀ ≅ L₁)
    (d₀ : K₀ ≅ G' ⋙ K') (d₁ : K₁ ≅ K ⋙ H') (d : K₀ ≅ K₁)
    (sm : G ⋙ L' ≅ L ⋙ H) (sa : G' ⋙ K' ≅ K ⋙ H')
    (hsm : sm = c₀.symm ≪≫ c ≪≫ c₁) (hsa : sa = d₀.symm ≪≫ d ≪≫ d₁)
    (h₀ : ComparisonCompositionEquation sG sL' s₀ c₀ d₀)
    (h₁ : ComparisonCompositionEquation sL sH s₁ c₁ d₁)
    (h : ComparisonTransportEquation s₀ s₁ c d) :
    ComparisonCubeEquation sL sL' sG sH sm sa := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc] using
    comparisonCube_app_of_composition sL sL' sG sH s₀ s₁ c₀ c₁ c d₀ d₁ d sm sa
      hsm hsa h₀ h₁ h X

end CategoryTheory.Functor
