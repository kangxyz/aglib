/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Section.Basic
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Section.ComposedPullbackLineTensor
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# Original coefficient and section under composed pullback

The original coefficient-section composite is retained. Its tensor pullback
square is derived at variable schemes rather than supplied after specializing
to an exceptional chart.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport the original coefficient followed by insertion of the original section. -/
theorem positiveSection_composedCoefficient_transport {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : f ≫ b = c)
    (L : Invertible.LineBundle Z) (N : Invertible.LineBundle Y)
    (M : Z.Modules) (φ : M ⟶ L.val)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ N.val) :
    let e := pullbackComp f b ≪≫ pullbackCongr hc
    let V := Invertible.tensorLineBundle X (Invertible.pullbackLineBundle c L)
      (Invertible.pullbackLineBundle f N)
    @Eq (@Quiver.Hom X.Modules (inferInstance : Quiver X.Modules)
      ((pullback f).obj ((pullback b).obj M)) V.val)
      ((pullback f).map ((pullback b).map φ ≫
        (positiveCartierTensorSection Y N.val s).app ((pullback b).obj L.val) ≫
        (tensorSheafBraiding Y N.val ((pullback b).obj L.val)).hom) ≫
        (Invertible.PullbackTensor.Local.pullbackLineBundleTensorIso f
          (Invertible.pullbackLineBundle b L) N ≪≫
          tensorSheafIso X (e.app L.val) (Iso.refl _)).hom)
      ((pullback f).map ((pullback b).map φ) ≫ e.hom.app L.val ≫
        (positiveCartierTensorSection X ((pullback f).obj N.val)
          ((pullbackUnitIso f).inv ≫ (pullback f).map s)).app
          ((pullback c).obj L.val) ≫
        (tensorSheafBraiding X ((pullback f).obj N.val) ((pullback c).obj L.val)).hom) := by
  apply positiveSection_composedPullbackLineTensor_transport f b c hc L N
    ((pullback f).obj ((pullback b).obj M))
    ((pullback f).map ((pullback b).map φ ≫
      (positiveCartierTensorSection Y N.val s).app ((pullback b).obj L.val) ≫
      (tensorSheafBraiding Y N.val ((pullback b).obj L.val)).hom))
    ((pullback f).map ((pullback b).map φ)) s
  rw [Functor.map_comp, Category.assoc, pullback_positiveSection]

end AlgebraicGeometry.Scheme.Modules
