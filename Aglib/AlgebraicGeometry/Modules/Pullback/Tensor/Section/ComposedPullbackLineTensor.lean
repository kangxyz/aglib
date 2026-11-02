/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Section.ComposedLineTensor
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# Original section transport from the original target scheme

The given section remains the original map on the target scheme. Its native
pullback-unit composite is formed at variable schemes before specialization,
preserving the original exceptional section and its normalization.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Specialize original line transport using the original pullback-composition component. -/
theorem positiveSection_composedPullbackLineTensor_transport {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : f ≫ b = c)
    (L : Invertible.LineBundle Z) (N : Invertible.LineBundle Y) (M : X.Modules)
    (g : M ⟶ (pullback f).obj
      (Invertible.tensorLineBundle Y (Invertible.pullbackLineBundle b L) N).val)
    (ψ : M ⟶ (pullback f).obj ((pullback b).obj L.val))
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ N.val)
    (hg : g ≫ pullbackTensorMap f ((pullback b).obj L.val) N.val =
      ψ ≫ (positiveCartierTensorSection X ((pullback f).obj N.val)
          ((pullbackUnitIso f).inv ≫ (pullback f).map s)).app
        ((pullback f).obj ((pullback b).obj L.val)) ≫
      (tensorSheafBraiding X ((pullback f).obj N.val)
        ((pullback f).obj ((pullback b).obj L.val))).hom) :
    let e := pullbackComp f b ≪≫ pullbackCongr hc
    g ≫ (Invertible.PullbackTensor.Local.pullbackLineBundleTensorIso f
        (Invertible.pullbackLineBundle b L) N ≪≫
        tensorSheafIso X (e.app L.val) (Iso.refl _)).hom =
      ψ ≫ e.hom.app L.val ≫
        (positiveCartierTensorSection X ((pullback f).obj N.val)
          ((pullbackUnitIso f).inv ≫ (pullback f).map s)).app
          ((pullback c).obj L.val) ≫
        (tensorSheafBraiding X ((pullback f).obj N.val) ((pullback c).obj L.val)).hom := by
  exact positiveSection_composedLineTensor_transport f b c hc L N M g ψ
    ((pullbackUnitIso f).inv ≫ (pullback f).map s) hg

end AlgebraicGeometry.Scheme.Modules
