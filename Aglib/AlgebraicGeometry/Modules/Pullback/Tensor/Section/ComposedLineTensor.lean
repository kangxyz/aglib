/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Section.LineTensor
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# Original section transport along a composed pullback of the same line

The native pullback composition and the given original triangle identify
the two retained pullback lines before specializing to a surface chart.
No new comparison map or replacement scheme is constructed.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Specialize original line transport using the original pullback-composition component. -/
theorem positiveSection_composedLineTensor_transport {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : f ≫ b = c)
    (L : Invertible.LineBundle Z) (N : Invertible.LineBundle Y) (M : X.Modules)
    (g : M ⟶ (pullback f).obj
      (Invertible.tensorLineBundle Y (Invertible.pullbackLineBundle b L) N).val)
    (ψ : M ⟶ (pullback f).obj ((pullback b).obj L.val))
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ (pullback f).obj N.val)
    (hg : g ≫ pullbackTensorMap f ((pullback b).obj L.val) N.val =
      ψ ≫ (positiveCartierTensorSection X ((pullback f).obj N.val) s).app
        ((pullback f).obj ((pullback b).obj L.val)) ≫
      (tensorSheafBraiding X ((pullback f).obj N.val)
        ((pullback f).obj ((pullback b).obj L.val))).hom) :
    let e := pullbackComp f b ≪≫ pullbackCongr hc
    g ≫ (Invertible.PullbackTensor.Local.pullbackLineBundleTensorIso f
        (Invertible.pullbackLineBundle b L) N ≪≫
        tensorSheafIso X (e.app L.val) (Iso.refl _)).hom =
      ψ ≫ e.hom.app L.val ≫
        (positiveCartierTensorSection X ((pullback f).obj N.val) s).app
          ((pullback c).obj L.val) ≫
        (tensorSheafBraiding X ((pullback f).obj N.val) ((pullback c).obj L.val)).hom := by
  intro e
  have h := positiveSection_lineTensor_transport f (Invertible.pullbackLineBundle b L) N
    (Invertible.pullbackLineBundle c L) (e.app L.val) M g ψ s hg
  simpa only [Invertible.pullbackLineBundle, Iso.app_hom] using h

end AlgebraicGeometry.Scheme.Modules
