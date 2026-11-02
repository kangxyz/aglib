/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.SpanFactorized
public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.SpanComponent

/-! # Quasi-isomorphism descent of the original Godement span

The complete factorized span and its original degree value are imported from
focused proof leaves. This leaf retains the original quasi-isomorphism descent.
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

lemma open_unit_span (K : CochainComplex.Plus X.Modules) :
    restrictedPullbackPushforwardPlusUnit f j K ≫ (openPullbackPushforwardComparison a b f j h
      K).hom ≫
        openBaseChangeGlobalLeg a b f K =
      (pullbackPushforwardPlusUnit b).app
          ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K) ≫
        openBaseChangeLocalLeg a b f j h K := by
  rw [restrictedPullbackPushforwardPlusUnit_factor, pullbackPushforwardPlusUnit_app]
  exact open_unit_span_factorized a b f j h K

include h in
theorem pullbackPushforwardPlusUnit_restrict_quasiIso (K : CochainComplex.Plus X.Modules)
    (hK : QuasiIso ((pullbackPushforwardPlusUnit b).app
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K)).hom) :
    QuasiIso ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
      ((pullbackPushforwardPlusUnit f).app K)).hom := by
  exact Plus.quasiIso_of_span (restrictedPullbackPushforwardPlusUnit f j K)
    (openPullbackPushforwardComparison a b f j h K).hom (openBaseChangeGlobalLeg a b f K)
    ((pullbackPushforwardPlusUnit b).app ((Scheme.Modules.restrictFunctor
      j).mapCochainComplexPlus.obj K))
    (openBaseChangeLocalLeg a b f j h K) (open_unit_span a b f j h K)
    (openBaseChangeGlobalLeg_quasiIso a b f K) hK (openBaseChangeLocalLeg_quasiIso a b f j h K)


end AlgebraicGeometry.Scheme.Modules.Godement
