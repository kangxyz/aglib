/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplexPlus.Functoriality
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PullbackPushforward
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

/-! # The original cartesian open comparisons and unit

This leaf retains the original mathematical values and declarations from the
open-base-change module. The compatibility facade retains the source provenance.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Godement

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

/-- Open restriction after direct image agrees with direct image after restriction in the
supplied cartesian square. -/
def openPushPlusIso :
    (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus ≅
      (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus ⋙
        (Scheme.Modules.pushforward b).mapCochainComplexPlus :=
  (Functor.mapCochainComplexPlusCompIso (Scheme.Modules.pushforward f)
    (Scheme.Modules.restrictFunctor j)).symm ≪≫
    NatIso.mapCochainComplexPlus (cartesianOpenBaseChange a b f j h) ≪≫
    Functor.mapCochainComplexPlusCompIso (Scheme.Modules.restrictFunctor a)
      (Scheme.Modules.pushforward b)

/-- The bounded-below pullback/restriction comparison for the supplied cartesian open square. -/
def openPullPlusIso :
    (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus ⋙
        (Scheme.Modules.pullback b).mapCochainComplexPlus ≅
      (Scheme.Modules.pullback f).mapCochainComplexPlus ⋙
        (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus :=
  (Functor.mapCochainComplexPlusCompIso (Scheme.Modules.restrictFunctor j)
    (Scheme.Modules.pullback b)).symm ≪≫
    NatIso.mapCochainComplexPlus (asIso (cartesianPullbackBaseChangeMate a b f j h)) ≪≫
    Functor.mapCochainComplexPlusCompIso (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctor a)

lemma open_geometric_unit (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
        ((Plus.pullbackPushforwardUnit f).app K) ≫
        (openPushPlusIso a b f j h).hom.app
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K) =
      (Plus.pullbackPushforwardUnit b).app ((Scheme.Modules.restrictFunctor
        j).mapCochainComplexPlus.obj K) ≫
        (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
          ((openPullPlusIso a b f j h).hom.app K) := by
  apply ObjectProperty.hom_ext
  apply HomologicalComplex.Hom.ext
  funext n
  exact cartesianOpenBaseChange_pullback_unit a b f j h (K.obj.X n)

end AlgebraicGeometry.Scheme.Modules.Godement
