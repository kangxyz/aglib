/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Prefactor

/-!
# The native chart prefactor on equal actual source opens

The original restriction congruence transports the same native comparison.
Only equality of the actual source morphisms is used; no replacement model
or resolution comparison is introduced.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Reflexive restriction congruence is the original identity on every module. -/
theorem canonicalRestrictionCongr_refl {W X : Scheme.{u}} (a : W ⟶ X)
    [IsOpenImmersion a] (M : X.Modules) :
    (restrictFunctorCongr (rfl : a = a)).hom.app M = 𝟙 (M.restrict a) := by
  apply Scheme.Modules.hom_ext
  intro V
  rw [restrictFunctorCongr_hom_app_app]
  change M.presheaf.map (𝟙 _) = 𝟙 _
  exact M.presheaf.map_id _

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance chartPrefactorCongruenceStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

/-- Equality of actual source opens retains the original native prefactor in the same degree. -/
theorem closedImmersionChartModelHomologyIsoInDegree_congr
    {W X V P : Scheme.{u}} (f : X ⟶ P) [IsClosedImmersion f]
    {L : P.Modules} (J : InjectiveResolution L)
    (a a' : W ⟶ X) [IsOpenImmersion a] [IsOpenImmersion a']
    (j : V ⟶ P) [IsOpenImmersion j] (b : W ⟶ V) [IsClosedImmersion b]
    (h : IsPullback a b f j) (h' : IsPullback a' b f j)
    (ha : a = a') (n m : ℤ) (hnm : n = m) :
    (restrictFunctorCongr ha).hom.app
        ((DerivedCategory.Plus.homologyFunctor X.Modules n).obj
          ((closedImmersionRightAdjoint f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj L))) ≫
      (closedImmersionChartModelHomologyIsoInDegree f J a' j b h' n m hnm).hom =
    (closedImmersionChartModelHomologyIsoInDegree f J a j b h n m hnm).hom := by
  subst a'
  rw [canonicalRestrictionCongr_refl, Category.id_comp]

end AlgebraicGeometry.Scheme.Modules
