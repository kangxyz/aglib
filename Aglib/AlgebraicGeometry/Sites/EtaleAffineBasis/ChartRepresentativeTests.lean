/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitGeometry

/-! # Original unit test maps of relative chart representatives -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology EtaleCohomology.Continuity

/-- The original pullback test map determined by a chart representative. -/
def relativeChartTest {X S : Scheme.{u}} (f : S ⟶ X) (W : S.Etale) (U : X.Etale)
    (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom ≫ f) :
    W ⟶ (siteBaseChange f).obj U :=
  MorphismProperty.Over.homMk (pullback.lift a W.hom ha)
    (pullback.lift_snd _ _ _) (by trivial)

/-- The representative recovered from this test has its original relative arrow. -/
theorem unitRepresentativeArrow_relativeChartTest {X S : Scheme.{u}} (f : S ⟶ X)
    (W : S.Etale) (U : X.Etale) (a : W.left ⟶ U.left)
    (ha : a ≫ U.hom = W.hom ≫ f) :
    unitRepresentativeArrow f (relativeChartTest f W U a ha) = Over.homMk a ha := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- Restricting a representative restricts its original unit test map. -/
theorem relativeChartTest_precomp {X S : Scheme.{u}} (f : S ⟶ X)
    {W Z : S.Etale} (g : Z ⟶ W) (U : X.Etale) (a : W.left ⟶ U.left)
    (ha : a ≫ U.hom = W.hom ≫ f) :
    g ≫ relativeChartTest f W U a ha =
      relativeChartTest f Z U (g.left ≫ a)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ g.left ≫ z) ha).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun z ↦ z ≫ f) (MorphismProperty.Over.w g))))) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ g.left ≫ z) (pullback.lift_fst _ _ _)).trans
        (pullback.lift_fst _ _ _).symm)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ g.left ≫ z) (pullback.lift_snd _ _ _)).trans
        ((MorphismProperty.Over.w g).trans (pullback.lift_snd _ _ _).symm))

end AlgebraicGeometry.Scheme.EtaleAffineBasis
