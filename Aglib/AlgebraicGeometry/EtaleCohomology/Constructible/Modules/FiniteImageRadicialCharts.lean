/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageRadicialModules
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageClosedComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant

/-! # Actual constant trivializations descended through finite radicial maps

The whole original unit and counit descend an actual constant isomorphism.
The chart assembly explicitly requires actual target charts and trivializations
on their entire source pullbacks; it does not assume or assert a geometric
chart-descent theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]
  {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [UniversallyInjective f] [Surjective f]

/-- An actual constant isomorphism after radicial pullback descends via the
original fully faithful adjunction unit, retaining its original module value. -/
def finiteRadicialConstantIsoOfPullback (F : ModuleSheaf R X) (M : ModuleCat.{u + 1} R)
    (e : (moduleInverseImage R f).obj F ≅
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    F ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M :=
  (finiteRadicialModuleUnitIso R f).app F ≪≫
    (moduleDirectImage R f).mapIso (e ≪≫ (moduleInverseImageConstantIso R f).symm.app M) ≪≫
    ((finiteRadicialModuleUnitIso R f).app
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)).symm

/-- A constant original coefficient has a constant original finite radicial
direct image, with the same module and without any Noetherian hypothesis. -/
def finiteRadicialDirectImageConstantIso (F : ModuleSheaf R Y)
    (M : ModuleCat.{u + 1} R)
    (e : F ≅ (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    (moduleDirectImage R f).obj F ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M :=
  finiteRadicialConstantIsoOfPullback R f _ M
    ((finiteRadicialModuleCounitIso R f).app F ≪≫ e)

/-- Given actual descended etale charts and actual constant isomorphisms on
their entire pullbacks, the original finite radicial direct image is FLC. -/
theorem isFiniteTypeLocallyConstant_finiteRadicialDirectImage_of_charts
    (F : ModuleSheaf R Y) (I : Type u) (V : I → X.Etale)
    (hV : ∀ x : X, ∃ a, ∃ y : (V a).left, (V a).hom y = x)
    (M : I → ModuleCat.{u + 1} R) (hM : ∀ a, Module.Finite R (M a))
    (e : ∀ a, (moduleInverseImage R (pullback.fst f (V a).hom)).obj F ≅
      (constantSheaf (pullback f (V a).hom).smallEtaleTopology
        (ModuleCat.{u + 1} R)).obj (M a)) :
    IsFiniteTypeLocallyConstant ((moduleDirectImage R f).obj F) := by
  refine ⟨{ index := I
            chart := V
            covers := hV
            value := M
            finite_value := hM
            trivialization := ?_ }⟩
  intro a
  let : MorphismProperty.IsStableUnderBaseChange (@UniversallyInjective.{u}) :=
    UniversallyInjective.isStableUnderBaseChange
  let : UniversallyInjective (pullback.snd f (V a).hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @UniversallyInjective.{u}) (IsPullback.of_hasPullback f (V a).hom)
      ‹UniversallyInjective f›
  exact (finiteImageBaseChangeIso R f (pullback.snd f (V a).hom) (V a).hom
    (pullback.fst f (V a).hom) (IsPullback.of_hasPullback f (V a).hom)).app F ≪≫
      finiteRadicialDirectImageConstantIso R (pullback.snd f (V a).hom) _ (M a) (e a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
