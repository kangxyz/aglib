/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.Geometry
public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.QuasiIso
public import Aglib.CategoryTheory.Functor.NatTrans.UnitInsertionSpan

/-! # The first Godement unit square under cartesian open base change

Comparison naturality transports the original geometric unit square along the
Godement augmentation. The whole square and its evaluation are proved while
the categories and functors remain variable.
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

lemma open_component_first_square (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (((Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (K.obj.X n))) ≫
        (Scheme.Modules.restrictFunctor j).map ((Scheme.Modules.pushforward f).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n))) ≫
      (cartesianOpenBaseChange a b f j h).hom.app
        (((godementTotalPlus U).obj
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).obj.X n) =
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
      ((Scheme.Modules.restrictFunctor j).obj (K.obj.X n)) ≫
    (Scheme.Modules.pushforward b).map
      ((cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
        (Scheme.Modules.restrictFunctor a).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n)) := by
  have hw := NatTrans.unitInsertion_first_square_point_map
      ((Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus)
      (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus
      (Scheme.Modules.pushforward b).mapCochainComplexPlus
      (openPushPlusIso a b f j h).hom
      ((godementTotalPlusUnit U).app
        ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
        ((Plus.pullbackPushforwardUnit f).app K))
      ((Plus.pullbackPushforwardUnit b).app
        ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))
      ((openPullPlusIso a b f j h).hom.app K)
      (open_geometric_unit a b f j h K)
      (CochainComplex.Plus.ι V.Modules ⋙ HomologicalComplex.eval V.Modules (.up ℤ) n)
  exact hw

end AlgebraicGeometry.Scheme.Modules.Godement
