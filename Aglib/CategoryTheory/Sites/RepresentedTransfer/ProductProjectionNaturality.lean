/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.RepresentedTransfer.OverProducts

/-! # Naturality of the projections of the original product test -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty.Over

universe c h

variable {C : Type c} [Category.{h} C] [HasPullbacks C]
  (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  {X : C}

/-- The original first projection is natural in the varying product factor. -/
@[reassoc]
theorem productTest_map_fst (V : P.Over ⊤ X) {U W : P.Over ⊤ X} (f : U ⟶ W) :
    (productTest P V).map f ≫ productFst P V W = productFst P V U ≫ f := by
  exact (mapPullbackAdj P ⊤ V.hom V.prop trivial).counit.naturality f

/-- Mapping the varying factor preserves the original second projection. -/
@[reassoc]
theorem productTest_map_snd (V : P.Over ⊤ X) {U W : P.Over ⊤ X} (f : U ⟶ W) :
    (productTest P V).map f ≫ productSnd P V W = productSnd P V U := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _

end CategoryTheory.MorphismProperty.Over
