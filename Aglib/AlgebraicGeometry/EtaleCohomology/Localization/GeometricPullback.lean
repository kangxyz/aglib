/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleShortExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleRefinementCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianExchangeMate
public import Aglib.CategoryTheory.Adjunction.LocalizationPullback
public import Aglib.Algebra.Homology.ShortComplex.LocalizationPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Exactness

/-! # Geometric inverse image of the original module localization sequence -/
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

/-- The actual open Cartesian comparison has the original inverse-image mate. -/
theorem mate_moduleLocalizationPullbackOpen :
    mateEquiv (moduleLowerShriekAdjunction j Λ) (moduleLowerShriekAdjunction j' Λ)
      (TwoSquare.mk _ _ _ _ (moduleLowerShriekCartesianBaseChangeIso g j' j f hj Λ).inv) =
    TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f g j j' hj.w).hom :=
  inverseComparison_mate_of_conjugacy
    (moduleLowerShriekAdjunction j Λ) (moduleLowerShriekAdjunction j' Λ)
    (moduleInverseImageAdjunction g Λ) (moduleInverseImageAdjunction f Λ)
    (moduleLowerShriekCartesianBaseChangeIso g j' j f hj Λ)
    (moduleCartesianExchangeIso g j' j f hj Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f g j j' hj.w).hom)
    (conjugateEquiv_moduleLowerShriekCartesianBaseChangeIso_hom g j' j f hj Λ)
    (moduleCartesianExchangeIso_hom g j' j f hj Λ)

/-- Original Cartesian open base change followed by the original inverse-image square. -/
def moduleLocalizationPullbackFirstIso (M : ModuleSheaf X Λ) :
    (moduleInverseImage f Λ).obj
      ((moduleLowerShriek j Λ).obj ((moduleInverseImage j Λ).obj M)) ≅
    (moduleLowerShriek j' Λ).obj
      ((moduleInverseImage j' Λ).obj ((moduleInverseImage f Λ).obj M)) :=
  (moduleLowerShriekCartesianBaseChangeIso g j' j f hj Λ).app
      ((moduleInverseImage j Λ).obj M) ≪≫
    (moduleLowerShriek j' Λ).mapIso ((moduleInverseImageSquareIso Λ f g j j' hj.w).app M)

/-- The third arrow is the actual direct-image mate, not a chosen isomorphism. -/
def moduleLocalizationPullbackThirdMap (M : ModuleSheaf X Λ) :
    (moduleInverseImage f Λ).obj
      ((moduleDirectImage i Λ).obj ((moduleInverseImage i Λ).obj M)) ⟶
    (moduleDirectImage i' Λ).obj
      ((moduleInverseImage i' Λ).obj ((moduleInverseImage f Λ).obj M)) :=
  (moduleBaseChangeMap Λ i i' f k hi.w.symm).app ((moduleInverseImage i Λ).obj M) ≫
    (moduleDirectImage i' Λ).map
      ((moduleInverseImageSquareIso Λ i i' f k hi.w.symm).inv.app M)

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
/-- Both original mate equations are retained as one shared abstract input. -/
theorem moduleLocalizationPullback_mates :
    LocalizationPullbackMateEquations
      (moduleLowerShriekAdjunction j Λ) (moduleLowerShriekAdjunction j' Λ)
      (moduleInverseImageAdjunction i Λ) (moduleInverseImageAdjunction i' Λ)
      (moduleLowerShriekCartesianBaseChangeIso g j' j f hj Λ)
      (moduleInverseImageSquareIso Λ f g j j' hj.w)
      (moduleInverseImageSquareIso Λ i i' f k hi.w.symm).symm
      (moduleBaseChangeMap Λ i i' f k hi.w.symm) :=
  ⟨mate_moduleLocalizationPullbackOpen j j' f g hj Λ, rfl⟩

/-- The original two adjunction maps form a geometric pullback comparison of whole sequences. -/
def moduleLocalizationPullbackMap
    (hc : Set.range j = (Set.range i)ᶜ) (hc' : Set.range j' = (Set.range i')ᶜ)
    (M : ModuleSheaf X Λ) :
    (moduleLocalizationShortComplex j Λ i hc M).map (moduleInverseImage f Λ) ⟶
      moduleLocalizationShortComplex j' Λ i' hc' ((moduleInverseImage f Λ).obj M) :=
  localizationSequencePullbackMap
    (moduleLowerShriekAdjunction j Λ) (moduleLowerShriekAdjunction j' Λ)
    (moduleInverseImageAdjunction i Λ) (moduleInverseImageAdjunction i' Λ)
    (moduleLowerShriekCartesianBaseChangeIso g j' j f hj Λ)
    (moduleInverseImageSquareIso Λ f g j j' hj.w)
    (moduleInverseImageSquareIso Λ i i' f k hi.w.symm).symm
    (moduleBaseChangeMap Λ i i' f k hi.w.symm)
    (moduleLocalizationPullback_mates j i j' i' f g k hj hi Λ) M
    (moduleLocalization_counit_comp_unit j Λ i hc M)
    (moduleLocalization_counit_comp_unit j' Λ i' hc' ((moduleInverseImage f Λ).obj M))

/-- Exact inverse image and the original open comparison force the actual third map invertible. -/
def moduleLocalizationPullbackIso
    (hc : Set.range j = (Set.range i)ᶜ) (hc' : Set.range j' = (Set.range i')ᶜ)
    (M : ModuleSheaf X Λ) :
    (moduleLocalizationShortComplex j Λ i hc M).map (moduleInverseImage f Λ) ≅
      moduleLocalizationShortComplex j' Λ i' hc' ((moduleInverseImage f Λ).obj M) :=
  localizationSequencePullbackIso
    (moduleLowerShriekAdjunction j Λ) (moduleLowerShriekAdjunction j' Λ)
    (moduleInverseImageAdjunction i Λ) (moduleInverseImageAdjunction i' Λ)
    (moduleLowerShriekCartesianBaseChangeIso g j' j f hj Λ)
    (moduleInverseImageSquareIso Λ f g j j' hj.w)
    (moduleInverseImageSquareIso Λ i i' f k hi.w.symm).symm
    (moduleBaseChangeMap Λ i i' f k hi.w.symm)
    (moduleLocalizationPullback_mates j i j' i' f g k hj hi Λ) M
    (moduleLocalization_counit_comp_unit j Λ i hc M)
    (moduleLocalization_counit_comp_unit j' Λ i' hc' ((moduleInverseImage f Λ).obj M))
    ((moduleLocalization_shortExact j Λ i hc M).map_of_exact (moduleInverseImage f Λ))
    (moduleLocalization_shortExact j' Λ i' hc' ((moduleInverseImage f Λ).obj M))
end AlgebraicGeometry.Scheme.EtaleCohomology
