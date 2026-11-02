/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.SpanComponent

/-! # The original factorized Godement unit span

The component is the evaluated complete generic span on the original data.
The original inclusion and equality in every degree give the whole equality.
The compatibility facade retains the original source provenance.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.Godement

attribute [local instance] openBaseChangeDerivedStandard

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

lemma open_unit_span_factorized (K : CochainComplex.Plus X.Modules) :
    ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
        ((Plus.pullbackPushforwardUnit f).app K) ≫
      ((Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus).map
          ((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))) ≫
      (openPullbackPushforwardComparison a b f j h K).hom ≫ openBaseChangeGlobalLeg a b f K =
    ((Plus.pullbackPushforwardUnit b).app
        ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K) ≫
      (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
        ((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
          ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K)))) ≫
      openBaseChangeLocalLeg a b f j h K := by
  apply ObjectProperty.hom_ext
  apply HomologicalComplex.Hom.ext
  funext n
  exact open_unit_span_component a b f j h K n

end AlgebraicGeometry.Scheme.Modules.Godement
