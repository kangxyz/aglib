/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Symmetric


/-!
# AlgebraicGeometry / Modules / Invertible / PullbackTensor / Frame

Source: `Normal/Frames.lean`.
Incoming SHA256: `2677a81f189d5b81153161a453c4e272def7d5bcaa884dc0a99622c0121bd02b`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y)
  (e : SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj L.val)

/-- Evaluation against the given actual pulled-back frame trivializes the pulled-back dual.
All arrows are the native unit, tensor comparison, braiding, and evaluation arrows. -/
def dualPullbackFrame :
    SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj (dualLineBundle Y L).val :=
  ((tensorSheafLeftUnit X ((Scheme.Modules.pullback f).obj (dualLineBundle Y L).val)).symm ≪≫
    tensorSheafIso X e (Iso.refl _) ≪≫
    tensorSheafBraiding X ((Scheme.Modules.pullback f).obj L.val)
      ((Scheme.Modules.pullback f).obj (dualLineBundle Y L).val) ≪≫
    (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle Y L) L).symm ≪≫
    (Scheme.Modules.pullback f).mapIso (dualEvaluationIso Y L) ≪≫ pullbackUnitIso f).symm
/-- The actual dual frame is inverse to evaluation against the original frame. -/
@[reassoc]
theorem dualPullbackFrame_evaluation :
    (dualPullbackFrame f L e).hom ≫
        (tensorSheafLeftUnit X ((Scheme.Modules.pullback f).obj (dualLineBundle Y L).val)).inv ≫
        (tensorSheafIso X e (Iso.refl _)).hom ≫
        (tensorSheafBraiding X ((Scheme.Modules.pullback f).obj L.val)
          ((Scheme.Modules.pullback f).obj (dualLineBundle Y L).val)).hom ≫
        (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle Y L) L).inv ≫
        (Scheme.Modules.pullback f).map (dualEvaluationIso Y L).hom ≫ (pullbackUnitIso f).hom =
      𝟙 (SheafOfModules.unit X.ringCatSheaf) :=
  (dualPullbackFrame f L e).hom_inv_id

end AlgebraicGeometry.Scheme.Modules.Invertible
