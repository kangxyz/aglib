/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! # A coproduct of two actual zero objects

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5NativePhiObjects.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`a0c31550c8b4ac9090c49b8d681d0fb83eb6f2232085781c80bd9306a82556fa`.
Selected declarations: coprod_isZero.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Limits

lemma coprod_isZero {C : Type*} [Category C] [HasZeroMorphisms C] (A B : C)
    [HasBinaryCoproduct A B] (hA : IsZero A) (hB : IsZero B) : IsZero (A ⨿ B) := by
  rw [IsZero.iff_id_eq_zero]
  apply coprod.hom_ext
  · exact hA.eq_of_src _ _
  · exact hB.eq_of_src _ _

end CategoryTheory.Limits
