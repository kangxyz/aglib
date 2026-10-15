/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Abelian.Subcategory.Exact
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
/-! # Finite products in a Serre class

This is derived from extension closure using split short exact sequences;
it is not an additional assumption on a Serre class.
-/
@[expose] public section


noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

instance serre_isClosedUnderFiniteProducts : P.IsClosedUnderFiniteProducts := by
  let : P.IsClosedUnderBinaryProducts :=
    ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
      rintro _ ⟨F, hF⟩
      let e := (HasLimit.isoOfNatIso (diagramIsoPair F)).trans
        (biprod.isoProd (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)).symm
      exact P.prop_of_iso e.symm (P.prop_biprod (hF _) (hF _)))
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

end CategoryTheory.ObjectProperty
