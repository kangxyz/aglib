/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.GeometricPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleComplex
public import Aglib.Algebra.Homology.CochainComplexPlus.Single
public import Aglib.Algebra.Homology.ShortComplex.LocalizationPullbackComplex

/-! # Original geometric pullback comparison of localization complexes -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u
variable {U Z X U' Z' X' : Scheme.{u}}
  (j : U ⟶ X) (i : Z ⟶ X) (j' : U' ⟶ X') (i' : Z' ⟶ X')
  (f : X' ⟶ X) (g : U' ⟶ U) (k : Z' ⟶ Z)
  [IsOpenImmersion j] [IsOpenImmersion j'] [IsClosedImmersion i] [IsClosedImmersion i']
  (hj : IsPullback g j' j f) (hi : IsPullback k i' i f)
  (Λ : Type (u + 1)) [Ring Λ]
  (hc : Set.range j = (Set.range i)ᶜ) (hc' : Set.range j' = (Set.range i')ᶜ)

/-- The actual open and inverse-image comparisons assembled as an original natural iso. -/
def moduleLocalizationPullbackFirstNatIso :
    (moduleInverseImage j Λ ⋙ moduleLowerShriek j Λ) ⋙ moduleInverseImage f Λ ≅
      moduleInverseImage f Λ ⋙ (moduleInverseImage j' Λ ⋙ moduleLowerShriek j' Λ) :=
  localizationPullbackFirstNatIso
    (moduleLowerShriekCartesianBaseChangeIso g j' j f hj Λ)
    (moduleInverseImageSquareIso Λ f g j j' hj.w)

/-- The third natural iso has exactly the original closed exchange as its underlying map. -/
def moduleLocalizationPullbackThirdNatIso :
    (moduleInverseImage i Λ ⋙ moduleDirectImage i Λ) ⋙ moduleInverseImage f Λ ≅
      moduleInverseImage f Λ ⋙ (moduleInverseImage i' Λ ⋙ moduleDirectImage i' Λ) :=
  localizationPullbackThirdNatIso
    (moduleLowerShriekAdjunction j Λ) (moduleLowerShriekAdjunction j' Λ)
    (moduleInverseImageAdjunction i Λ) (moduleInverseImageAdjunction i' Λ)
    (moduleLowerShriekCartesianBaseChangeIso g j' j f hj Λ)
    (moduleInverseImageSquareIso Λ f g j j' hj.w)
    (moduleInverseImageSquareIso Λ i i' f k hi.w.symm).symm
    (moduleBaseChangeMap Λ i i' f k hi.w.symm)
    (moduleLocalizationPullback_mates j i j' i' f g k hj hi Λ)
    (moduleLocalization_counit_comp_unit j Λ i hc)
    (moduleLocalization_counit_comp_unit j' Λ i' hc')
    (fun M => (moduleLocalization_shortExact j Λ i hc M).map_of_exact
      (moduleInverseImage f Λ))
    (moduleLocalization_shortExact j' Λ i' hc')

/-- Degreewise geometric pullback identifies the original two-arrow localization complex. -/
def moduleLocalizationComplexPullbackIso (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationComplex j Λ i hc K).map (moduleInverseImage f Λ).mapCochainComplexPlus ≅
      moduleLocalizationComplex j' Λ i' hc'
        ((moduleInverseImage f Λ).mapCochainComplexPlus.obj K) :=
  localizationSequenceComplexPullbackIso
    (moduleLowerShriekAdjunction j Λ) (moduleLowerShriekAdjunction j' Λ)
    (moduleInverseImageAdjunction i Λ) (moduleInverseImageAdjunction i' Λ)
    (moduleLowerShriekCartesianBaseChangeIso g j' j f hj Λ)
    (moduleInverseImageSquareIso Λ f g j j' hj.w)
    (moduleInverseImageSquareIso Λ i i' f k hi.w.symm).symm
    (moduleBaseChangeMap Λ i i' f k hi.w.symm)
    (moduleLocalizationPullback_mates j i j' i' f g k hj hi Λ)
    (moduleLocalization_counit_comp_unit j Λ i hc)
    (moduleLocalization_counit_comp_unit j' Λ i' hc')
    (fun M => (moduleLocalization_shortExact j Λ i hc M).map_of_exact
      (moduleInverseImage f Λ))
    (moduleLocalization_shortExact j' Λ i' hc') K
    (moduleLocalizationComplex j Λ i hc K).zero
    (moduleLocalizationComplex j' Λ i' hc'
      ((moduleInverseImage f Λ).mapCochainComplexPlus.obj K)).zero

/-- The complete original sequence comparison is natural in the bounded-below complex. -/
theorem moduleLocalizationComplexPullbackIso_naturality
    {K L : CochainComplex.Plus (ModuleSheaf X Λ)} (a : K ⟶ L) :
    (moduleInverseImage f Λ).mapCochainComplexPlus.mapShortComplex.map
        (moduleLocalizationComplexMap j Λ i hc a) ≫
      (moduleLocalizationComplexPullbackIso j i j' i' f g k hj hi Λ hc hc' L).hom =
    (moduleLocalizationComplexPullbackIso j i j' i' f g k hj hi Λ hc hc' K).hom ≫
      moduleLocalizationComplexMap j' Λ i' hc'
        ((moduleInverseImage f Λ).mapCochainComplexPlus.map a) := by
  apply ShortComplex.hom_ext
  · exact (NatIso.mapCochainComplexPlus
      (moduleLocalizationPullbackFirstNatIso j j' f g hj Λ)).hom.naturality a
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (NatIso.mapCochainComplexPlus
      (moduleLocalizationPullbackThirdNatIso j i j' i' f g k hj hi Λ hc hc')).hom.naturality a
end AlgebraicGeometry.Scheme.EtaleCohomology
