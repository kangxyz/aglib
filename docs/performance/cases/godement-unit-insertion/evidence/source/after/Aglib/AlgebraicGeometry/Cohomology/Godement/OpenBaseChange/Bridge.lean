/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.Geometry

/-! # The original Godement bridge and its values

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

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

/-- The cartesian pullback comparison followed by the restricted Godement augmentation. -/
def openTotalBridge (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.pullback b).mapCochainComplexPlus.obj
        ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K) ⟶
      (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.obj
        ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)) :=
  (openPullPlusIso a b f j h).hom.app K ≫
    (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.map
      ((godementTotalPlusUnit U).app ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))

lemma openTotalBridge_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso (openTotalBridge a b f j h K).hom := by
  have : QuasiIso ((godementTotalPlusUnit U).app
      ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom :=
    godementTotalPlusUnit_quasiIso _ _
  have hres : QuasiIso ((Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.map
      ((godementTotalPlusUnit U).app
        ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))).hom := by
    exact Complex.restrict_quasiIso a
      ((godementTotalPlusUnit U).app
        ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom
  have hiso : IsIso ((openPullPlusIso a b f j h).hom.app K) := inferInstance
  let e := (CochainComplex.Plus.ι W.Modules).mapIso ((openPullPlusIso a b f j h).app K)
  have : IsIso ((openPullPlusIso a b f j h).hom.app K).hom := by
    change IsIso e.hom
    infer_instance
  unfold openTotalBridge
  change QuasiIso (((openPullPlusIso a b f j h).hom.app K).hom ≫
    ((Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.map _).hom)
  infer_instance

lemma restrictedTotalPlus_flasque (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    let J := (Scheme.Modules.restrictFunctor a).mapCochainComplexPlus.obj
      ((godementTotalPlus U).obj ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K))
    TopCat.Presheaf.IsFlasque (J.obj.X n).presheaf := by
  dsimp only
  let C := (Scheme.Modules.pullback f).mapCochainComplexPlus.obj K
  exact @Scheme.Modules.restrictModule_isFlasque W U a inferInstance
    (((godementTotalPlus U).obj C).obj.X n) (totalPlus_terms_isFlasque U C n)

lemma openTotalBridge_f (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (openTotalBridge a b f j h K).hom.f n =
      (cartesianPullbackBaseChangeMate a b f j h).app (K.obj.X n) ≫
        (Scheme.Modules.restrictFunctor a).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n) := rfl

end AlgebraicGeometry.Scheme.Modules.Godement
