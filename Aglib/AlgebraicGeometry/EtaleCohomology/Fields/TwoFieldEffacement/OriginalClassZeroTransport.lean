/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence

/-! # Original class zero along a specified composite map

The complete three-scheme construction retains the original class and its Ext
world. Equality with the actual target arrow is eliminated before constructing
inverse-image composition; native geometric consumers supply only their original
map equation, without rewriting a dependent cohomology carrier themselves.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u eX

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Original pullback zero is preserved along the specified composite arrow.
The intermediate and final cohomology use the original standard Ext worlds. -/
theorem original_class_zero_of_map_law
    {T W W' : Scheme.{u}} [HasExt.{eX} (AbelianSheaf.{u, u + 1} T)]
    (v : W' ⟶ W) (h : W ⟶ T) (g : W' ⟶ T) (hg : v ≫ h = g)
    (M : AbelianSheaf.{u, u + 1} T) (q : ℕ) (c : Sheaf.H.{eX} M q)
    (hc : cohomologyPullback.{u, eX, u + 2} h M q c = 0) :
    cohomologyPullback.{u, eX, u + 2} g M q c = 0 := by
  subst g
  apply (cohomologyMapIso_bijective ((inverseImageComp h v).app M) q).injective
  have hcomp := cohomologyPullback_comp.{u, eX, u + 2, u + 2} h v M q c
  rw [hc, map_zero] at hcomp
  exact hcomp.trans (map_zero _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
