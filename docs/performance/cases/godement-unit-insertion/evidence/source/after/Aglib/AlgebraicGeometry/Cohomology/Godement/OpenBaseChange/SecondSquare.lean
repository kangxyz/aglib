/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.SpanData
public import Aglib.CategoryTheory.Functor.NatTrans.UnitInsertionSpan

/-! # The second square of the original cartesian open Godement span

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5PositiveUnitOpen.lean`
at LOCAL Quillen `189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`5c431ecd8bb08af3ce18cc4d638cada3b8b8d1cde05b6044df1ecd8add2d3446`.
Selected declarations: augmentation_component_naturality, local_total_unit_component,
  open_component_second_square.

The complete augmentation equation is proved over variable categories before
specializing the literal bridge or evaluating a native complex and degree.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Godement

attribute [local instance] openBaseChangeDerivedStandard

private lemma augmentation_component_naturality {C : Type*} [Category C] [HasZeroMorphisms C]
    (T : CochainComplex.Plus C ⥤ CochainComplex.Plus C) (η : 𝟭 _ ⟶ T)
    (K L : CochainComplex.Plus C) (s : K ⟶ L) (n : ℤ) :
    s.hom.f n ≫ (η.app L).hom.f n = (η.app K).hom.f n ≫ (T.map s).hom.f n := by
  exact congrArg (fun q => q.hom.f n) (η.naturality s)


variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

lemma local_total_unit_component (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    ((cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
      (Scheme.Modules.restrictFunctor a).map
        (((godementTotalPlusUnit U).app
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n)) ≫
      ((godementTotalPlusUnit W).app (restrictedTotalPlus a f K)).hom.f n =
    ((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))).hom.f n ≫
        ((godementTotalPlus W).map (openTotalBridge a b f j h K)).hom.f n := by
  have hn := augmentation_component_naturality (godementTotalPlus W) (godementTotalPlusUnit W)
    ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))
    (restrictedTotalPlus a f K) (openTotalBridge a b f j h K) n
  have hb := congrArg
    (fun q => q ≫ ((godementTotalPlusUnit W).app (restrictedTotalPlus a f K)).hom.f n)
    (openTotalBridge_f a b f j h K n)
  have he := hb.symm.trans hn
  exact he

lemma open_component_second_square (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (Scheme.Modules.pushforward b).map
      ((cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
        (Scheme.Modules.restrictFunctor a).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n)) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlusUnit W).app (restrictedTotalPlus a f K)).hom.f n) =
    (Scheme.Modules.pushforward b).map
      (((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
        ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))).hom.f n) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlus W).map (openTotalBridge a b f j h K)).hom.f n) := by
  have ht := congrArg (Scheme.Modules.pushforward b).map
    (local_total_unit_component a b f j h K n)
  simpa only [Functor.map_comp] using ht


end AlgebraicGeometry.Scheme.Modules.Godement
