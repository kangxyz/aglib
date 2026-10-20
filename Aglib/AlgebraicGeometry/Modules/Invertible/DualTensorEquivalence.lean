/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual

/-!
# Tensor equivalence from an actual invertible module

Tensoring by the actual dual line bundle is an equivalence of the original
module-sheaf category of an arbitrary scheme. Its inverse tensors by the
original line bundle. The cancellation isomorphisms use the existing actual
evaluation, tensor braiding, associator and unit maps.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable (X : Scheme.{u})

/-- Tensoring by the actual dual is an equivalence, with tensoring by the
original line bundle as inverse. The two cancellation maps are its actual
evaluation and braiding maps. -/
def lineBundleDualTensorEquivalence (L : LineBundle X) : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk
    (tensorLeft (dualLineBundle X L).val) (tensorLeft L.val)
    (((tensorLeftTensor (C := X.Modules) L.val (dualLineBundle X L).val).symm ≪≫
      (tensoringLeft X.Modules).mapIso
        ((tensorSheafBraiding X L.val (dualLineBundle X L).val) ≪≫
          dualEvaluationIso X L) ≪≫ leftUnitorNatIso X.Modules).symm)
    ((tensorLeftTensor (C := X.Modules) (dualLineBundle X L).val L.val).symm ≪≫
      (tensoringLeft X.Modules).mapIso (dualEvaluationIso X L) ≪≫
        leftUnitorNatIso X.Modules)

end AlgebraicGeometry.Scheme.Modules.Invertible
