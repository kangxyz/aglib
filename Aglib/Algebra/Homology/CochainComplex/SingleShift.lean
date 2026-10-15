/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift


/-!
Source: `Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalLineRotation.lean` at LOCAL
Quillen `189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: cut_general; source ranges [[112, 116]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem chainMap_single_zero_to_shift_one_eq_zero (M N : C)
    (f : (CochainComplex.singleFunctor C 0).obj M ⟶
      ((CochainComplex.singleFunctor C 0).obj N)⟦(1 : ℤ)⟧) : f = 0 := by
  apply HomologicalComplex.from_single_hom_ext
  exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) (0 : ℤ) N (1 : ℤ) (by decide)).eq_of_tgt _ _

end CochainComplex
