/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryFaceEpimorphism
public import Aglib.CategoryTheory.EpiEquality
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryComparisonHeads

/-! # Exact component word of the original ordinary comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g)

/-- Unfold only the complete original comparison, retaining every map. -/
theorem sourceEtaleOrdinaryComparison_app_word (U : X.Etale)
    (F : AbelianSheaf.{u, u + 1} X) :
    (sourceEtaleOrdinaryComparison f f' g g' H U).app F =
      (SourceChartMates.sourceIso (sourceEtaleImageInverseIso f U) (inverseImage g)).hom.app F ≫
        (baseChangeMap (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
          (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm).app
            ((inverseImage U.hom).obj F) ≫
        (SourceChartMates.targetIso
          (G := directImage (pullback.snd U.hom g' ≫ f'))
          (inverseImageSquareIso U.hom ((siteBaseChange g').obj U).hom g'
            (pullback.fst U.hom g') pullback.condition.symm).symm
          (sourceEtaleImageInverseIso f' ((siteBaseChange g').obj U))).hom.app F :=
  (congrArg (fun z => z.app F) (sourceEtaleOrdinaryComparison_as_generic f f' g g' H U)).trans
    (SourceChartMates.comparison_app
      (inverseImageSquareIso U.hom ((siteBaseChange g').obj U).hom g'
        (pullback.fst U.hom g') pullback.condition.symm).symm
      (baseChangeMap (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
        (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
      (sourceEtaleImageInverseIso f U)
      (sourceEtaleImageInverseIso f' ((siteBaseChange g').obj U)) F)

/-- Epimorphy at precisely that original component word. -/
theorem sourceEtaleOrdinaryComparison_word_epi [Smooth g] (U : X.Etale)
    (n : ℕ) (hn : 0 < n) (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) : type_of% (
  sourceChartOrdinaryTransport_epi f f' g g' H U.hom
    ((inverseImage U.hom).obj F) n hn (sourceEtaleRestricted_killed U F n hF)
    ((SourceChartMates.sourceIso (sourceEtaleImageInverseIso f U) (inverseImage g)).app F)
    ((SourceChartMates.targetIso
      (G := directImage (pullback.snd U.hom g' ≫ f'))
      (inverseImageSquareIso U.hom ((siteBaseChange g').obj U).hom g'
        (pullback.fst U.hom g') pullback.condition.symm).symm
      (sourceEtaleImageInverseIso f' ((siteBaseChange g').obj U))).app F)
    ) :=
  sourceChartOrdinaryTransport_epi f f' g g' H U.hom
    ((inverseImage U.hom).obj F) n hn (sourceEtaleRestricted_killed U F n hF)
    ((SourceChartMates.sourceIso (sourceEtaleImageInverseIso f U) (inverseImage g)).app F)
    ((SourceChartMates.targetIso
      (G := directImage (pullback.snd U.hom g' ≫ f'))
      (inverseImageSquareIso U.hom ((siteBaseChange g').obj U).hom g'
        (pullback.fst U.hom g') pullback.condition.symm).symm
      (sourceEtaleImageInverseIso f' ((siteBaseChange g').obj U))).app F)

end AlgebraicGeometry.Scheme.EtaleCohomology
