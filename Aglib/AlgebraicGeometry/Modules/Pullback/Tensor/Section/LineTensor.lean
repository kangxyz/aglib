/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Pairing
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Section.Naturality
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# Original positive-section transport through retained tensor lines

The original pullback tensor comparison and the original other-factor
isomorphism transport an already proved section equation. All carriers are
retained line bundles on variable schemes before any blowup specialization.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport the original section equation through the original line tensor comparison. -/
theorem positiveSection_lineTensor_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P N : Invertible.LineBundle Y) (Q : Invertible.LineBundle X)
    (e : (pullback f).obj P.val ≅ Q.val) (M : X.Modules)
    (g : M ⟶ (pullback f).obj (Invertible.tensorLineBundle Y P N).val)
    (ψ : M ⟶ (pullback f).obj P.val)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ (pullback f).obj N.val)
    (hg : g ≫ pullbackTensorMap f P.val N.val =
      ψ ≫ (positiveCartierTensorSection X ((pullback f).obj N.val) s).app
        ((pullback f).obj P.val) ≫
      (tensorSheafBraiding X ((pullback f).obj N.val) ((pullback f).obj P.val)).hom) :
    g ≫ (Invertible.PullbackTensor.Local.pullbackLineBundleTensorIso f P N ≪≫
        tensorSheafIso X e (Iso.refl _)).hom =
      ψ ≫ e.hom ≫
        (positiveCartierTensorSection X ((pullback f).obj N.val) s).app Q.val ≫
        (tensorSheafBraiding X ((pullback f).obj N.val) Q.val).hom := by
  have hn := positiveSection_otherFactor ((pullback f).obj P.val) Q.val
    ((pullback f).obj N.val) s e.hom
  have ht := congrArg (fun z => z ≫ tensorSheafMap X e.hom
    (𝟙 ((pullback f).obj N.val))) hg
  have he := congrArg (fun z => ψ ≫ z) hn
  simpa only [Iso.trans_hom, Invertible.PullbackTensor.Local.pullbackLineBundleTensorIso_hom,
    tensorSheafIso_hom, Iso.refl_hom, Invertible.pullbackLineBundle, Category.assoc] using
      ht.trans (by simpa only [Category.assoc] using he)

end AlgebraicGeometry.Scheme.Modules
