/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryComponentWord
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.ChartComparisonEpimorphism

/-! # Cache the original ordinary component epimorphy at its actual map head -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge

/-- Specialize the original chart epimorphism at the original chart. -/
theorem sourceEtaleOrdinaryComparison_actual_epi
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (H : IsPullback g' f' f g) [Smooth g] (U : X.Etale)
    (n : ℕ) (hn : 0 < n) (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) : type_of% (
  sourceChartComparison_epi f f' g g' H U.hom
    (inverseImage U.hom) (inverseImage ((siteBaseChange g').obj U).hom)
    (sourceEtaleImage f U) (sourceEtaleImage f' ((siteBaseChange g').obj U))
    (inverseImageSquareIso U.hom ((siteBaseChange g').obj U).hom g'
      (pullback.fst U.hom g') pullback.condition.symm).symm
    (sourceEtaleImageInverseIso f U)
    (sourceEtaleImageInverseIso f' ((siteBaseChange g').obj U))
    (sourceEtaleOrdinaryComparison f f' g g' H U)
    (sourceEtaleOrdinaryComparison_as_generic f f' g g' H U) F n hn
    (sourceEtaleRestricted_killed U F n hF)
    ) :=
  sourceChartComparison_epi f f' g g' H U.hom
    (inverseImage U.hom) (inverseImage ((siteBaseChange g').obj U).hom)
    (sourceEtaleImage f U) (sourceEtaleImage f' ((siteBaseChange g').obj U))
    (inverseImageSquareIso U.hom ((siteBaseChange g').obj U).hom g'
      (pullback.fst U.hom g') pullback.condition.symm).symm
    (sourceEtaleImageInverseIso f U)
    (sourceEtaleImageInverseIso f' ((siteBaseChange g').obj U))
    (sourceEtaleOrdinaryComparison f f' g g' H U)
    (sourceEtaleOrdinaryComparison_as_generic f f' g g' H U) F n hn
    (sourceEtaleRestricted_killed U F n hF)

end AlgebraicGeometry.Scheme.EtaleCohomology
