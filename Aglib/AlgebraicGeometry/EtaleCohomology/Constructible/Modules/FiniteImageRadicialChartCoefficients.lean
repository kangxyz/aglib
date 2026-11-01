/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageRadicialCharts

/-! # Original finite image on a geometrically descended constant chart

The geometry supplies an actual map from the entire pullback chart to the
original trivializing chart. Native image composition, finite base change and
the original radicial image adjunction transport the same module value.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- The actual restricted finite radicial image is FLC when a surjective
etale target chart factors, after full pullback, through a constant source chart. -/
theorem isFiniteTypeLocallyConstant_radicialImage_restrict_of_chart
    {Y X U T W : Scheme.{u}}
    (f : Y ⟶ X) [IsFinite f] [Surjective f] [UniversallyInjective f]
    (j : U ⟶ X) (q : T ⟶ U) [Etale q] [Surjective q] (w : W ⟶ Y)
    (a : pullback f (q ≫ j) ⟶ W) (ha : a ≫ w = pullback.fst f (q ≫ j))
    (F : ModuleSheaf R Y) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (e : (moduleInverseImage R w).obj F ≅
      (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    IsFiniteTypeLocallyConstant
      ((moduleInverseImage R j).obj ((moduleDirectImage R f).obj F)) := by
  let ec : (moduleInverseImage R (pullback.fst f (q ≫ j))).obj F ≅
      (constantSheaf (pullback f (q ≫ j)).smallEtaleTopology
        (ModuleCat.{u + 1} R)).obj M :=
    eqToIso (congrArg (fun h => (moduleInverseImage R h).obj F) ha.symm) ≪≫
      (moduleInverseImageComp R w a).app F ≪≫
      (moduleInverseImage R a).mapIso e ≪≫ (moduleInverseImageConstantIso R a).app M
  let : MorphismProperty.IsStableUnderBaseChange (@UniversallyInjective.{u}) :=
    UniversallyInjective.isStableUnderBaseChange
  let : UniversallyInjective (pullback.snd f (q ≫ j)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @UniversallyInjective.{u}) (IsPullback.of_hasPullback f (q ≫ j))
      ‹UniversallyInjective f›
  refine ⟨{ index := PUnit.{u + 1}
            chart := fun _ => Scheme.Etale.mk q
            covers := fun x => ?_
            value := fun _ => M
            finite_value := fun _ => inferInstance
            trivialization := fun _ => ?_ }⟩
  · obtain ⟨y, hy⟩ := q.surjective x
    exact ⟨PUnit.unit, y, hy⟩
  · exact ((moduleInverseImageComp R j q).app ((moduleDirectImage R f).obj F)).symm ≪≫
      (finiteImageBaseChangeIso R f (pullback.snd f (q ≫ j)) (q ≫ j)
        (pullback.fst f (q ≫ j)) (IsPullback.of_hasPullback f (q ≫ j))).app F ≪≫
      finiteRadicialDirectImageConstantIso R (pullback.snd f (q ≫ j)) _ M ec

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
