/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.Bridge

/-! # The original objects and legs of the Godement span

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

attribute [local instance]
  AlgebraicGeometry.Scheme.Modules.Godement.openBaseChangeDerivedStandard

private lemma pushforward_godement_map_quasiIso {P Y : Scheme.{u}} (p : P ⟶ Y)
    {K M : CochainComplex.Plus P.Modules} (s : K ⟶ M) (hs : QuasiIso s.hom) :
    QuasiIso ((Scheme.Modules.pushforward p).mapCochainComplexPlus.map
      ((godementTotalPlus P).map s)).hom := by
  let := hs
  let : QuasiIso ((godementTotalPlus P).map s).hom := godementTotalPlus_map_quasiIso s
  exact Plus.pushforward_quasiIso_of_flasque p _ (totalPlus_terms_isFlasque P K)
    (totalPlus_terms_isFlasque P M)

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

/-- The resolved pullback/direct-image complex for f restricted along the open immersion j. -/
def restrictedPullbackPushforwardPlus (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus
  V.Modules :=
  (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj ((pullbackPushforwardPlus f).obj K)

/-- The resolved pullback/direct-image complex for b applied to the complex restricted along j. -/
def localPullbackPushforwardPlus (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus
  V.Modules :=
  (pullbackPushforwardPlus b).obj ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K)

/-- The restriction along a of the Godement total of the complex pulled back along f. -/
abbrev restrictedTotalPlus (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus W.Modules :=
  (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.obj
    ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))

/-- The common span target obtained by further Godement totalization and direct image of the
restricted source total. -/
def openBaseChangeSpanTarget (K : CochainComplex.Plus X.Modules) : CochainComplex.Plus V.Modules :=
  (Scheme.Modules.pushforward b).mapCochainComplexPlus.obj
    ((godementTotalPlus W).obj (restrictedTotalPlus a f K))

/-- The resolved pullback/direct-image unit after restriction along j. -/
def restrictedPullbackPushforwardPlusUnit (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K ⟶
      restrictedPullbackPushforwardPlus f j K :=
  (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map ((pullbackPushforwardPlusUnit
    f).app K)

/-- The cartesian open direct-image comparison on the resolved pullback complex. -/
def openPullbackPushforwardComparison (K : CochainComplex.Plus X.Modules) :
    restrictedPullbackPushforwardPlus f j K ≅
      (Scheme.Modules.pushforward b).mapCochainComplexPlus.obj (restrictedTotalPlus a f K) :=
  (openPushPlusIso a b f j h).app
    ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))

/-- The direct image of the Godement augmentation on the restricted source total. -/
def openBaseChangeGlobalLeg (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.pushforward b).mapCochainComplexPlus.obj (restrictedTotalPlus a f K) ⟶
      openBaseChangeSpanTarget a b f K :=
  (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
    ((godementTotalPlusUnit W).app (restrictedTotalPlus a f K))

/-- The direct image of the Godement-total map induced by the cartesian bridge. -/
def openBaseChangeLocalLeg (K : CochainComplex.Plus X.Modules) :
    localPullbackPushforwardPlus b j K ⟶ openBaseChangeSpanTarget a b f K :=
  (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
    ((godementTotalPlus W).map (openTotalBridge a b f j h K))

lemma restrictedPullbackPushforwardPlusUnit_factor (K : CochainComplex.Plus X.Modules) :
    restrictedPullbackPushforwardPlusUnit f j K =
      (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
          ((Plus.pullbackPushforwardUnit f).app K) ≫
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
          (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus).map
            ((godementTotalPlusUnit U).app
              ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)) := by
  unfold restrictedPullbackPushforwardPlusUnit
  rw [pullbackPushforwardPlusUnit_app, Functor.map_comp]
  rfl

lemma openBaseChangeGlobalLeg_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso (openBaseChangeGlobalLeg a b f K).hom := by
  have : QuasiIso ((godementTotalPlusUnit W).app (restrictedTotalPlus a f K)).hom :=
    godementTotalPlusUnit_quasiIso _ _
  exact Plus.pushforward_quasiIso_of_flasque b _
    (restrictedTotalPlus_flasque a f K) (totalPlus_terms_isFlasque W (restrictedTotalPlus a f K))

lemma openBaseChangeLocalLeg_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso (openBaseChangeLocalLeg a b f j h K).hom := by
  exact pushforward_godement_map_quasiIso b
    (K := (Scheme.Modules.pullback b).mapCochainComplexPlus.obj
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))
    (M := restrictedTotalPlus a f K) (openTotalBridge a b f j h K)
    (openTotalBridge_quasiIso a b f j h K)

end AlgebraicGeometry.Scheme.Modules.Godement
