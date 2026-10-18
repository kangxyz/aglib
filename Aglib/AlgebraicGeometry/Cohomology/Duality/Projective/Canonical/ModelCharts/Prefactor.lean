/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Model.OpenComposition.Homology

/-!
# Composition of the original chart source factors in a common degree

Only an actual integer-degree equality changes the native chart prefactor.
The same original direct-to-iterated restricted-resolution lift remains in
its composition equation.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry HomologicalComplex

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance chartPrefactorStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {W' W U V' V P : Scheme.{u}} (f : U ⟶ P) [IsClosedImmersion f]
  {L : P.Modules} (J : InjectiveResolution L)
  (a : W ⟶ U) (j : V ⟶ P) (b : W ⟶ V)
  [IsOpenImmersion a] [IsOpenImmersion j] [IsClosedImmersion b]
  (h : IsPullback a b f j)

/-- Original native chart-model comparison followed only by genuine homology-degree transport. -/
def closedImmersionChartModelHomologyIsoInDegree (n m : ℤ) (hnm : n = m) :
    ((DerivedCategory.Plus.homologyFunctor U.Modules n).obj
      ((closedImmersionRightAdjoint f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj L))).restrict a ≅
      (((closedImmersionRightAdjoint b).mapHomologicalComplex (.up ℤ)).obj
        (canonicalAmbientChartResolution J j).cochainComplex).homology m :=
  closedImmersionChartModelHomologyIso f J a j b h n ≪≫
    eqToIso (congrArg (fun k : ℤ =>
      (((closedImmersionRightAdjoint b).mapHomologicalComplex (.up ℤ)).obj
        (canonicalAmbientChartResolution J j).cochainComplex).homology k) hnm)

variable (c : W' ⟶ W) (k : V' ⟶ V) (d : W' ⟶ V')
  [IsOpenImmersion c] [IsOpenImmersion k] [IsClosedImmersion d]
  (h' : IsPullback c d b k)

/-- The actual native chart prefactors compose in the same genuine common degree. -/
theorem closedImmersionChartModelHomologyIsoInDegree_comp (n m : ℤ) (hnm : n = m) :
    (restrictFunctorComp c a).hom.app
        ((DerivedCategory.Plus.homologyFunctor U.Modules n).obj
          ((closedImmersionRightAdjoint f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj L))) ≫
      (restrictFunctor c).map
        (closedImmersionChartModelHomologyIsoInDegree f J a j b h n m hnm).hom ≫
      closedImmersionChartModelStepHomologyMap b (canonicalAmbientChartResolution J j)
        c k d h' m =
    (closedImmersionChartModelHomologyIsoInDegree f J (c ≫ a) (k ≫ j) d
      (h'.paste_horiz h) n m hnm).hom ≫
      homologyMap (((closedImmersionRightAdjoint d).mapHomologicalComplex (.up ℤ)).map
        (canonicalAmbientResolutionCompLift j k J).hom') m := by
  subst m
  simpa only [closedImmersionChartModelHomologyIsoInDegree, eqToIso_refl,
    Iso.trans_hom, Iso.refl_hom, Category.comp_id] using
    closedImmersionChartModelHomologyIso_comp f J a j b h c k d h' n

end AlgebraicGeometry.Scheme.Modules
