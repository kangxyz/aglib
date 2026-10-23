/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Original constant-sheaf unit under coefficient composition

The normalization is proved before specializing any geometric section carriers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite

namespace CategoryTheory

variable {C D B : Type*} [Category* C] [Category* D] [Category* B]
  (J : GrothendieckTopology C) [HasWeakSheafify J D] [HasWeakSheafify J B]
  (F : D ⥤ B) [J.PreservesSheafification F] [J.HasSheafCompose F]

/-- The original constant-composition isomorphism preserves the original unit. -/
theorem constantCommuteCompose_toSheafify (A : D) :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) F ≫
      ((constantCommuteCompose J F).hom.app A).hom =
    (Functor.constComp Cᵒᵖ A F).hom ≫
      toSheafify J ((Functor.const Cᵒᵖ).obj (F.obj A)) := by
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc, sheafComposeIso_inv_fac,
    ← toSheafify_naturality]

end CategoryTheory
