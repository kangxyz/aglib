/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ShortExact
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-! # A fixed-degree Serre induction for original right-derived images

The original connecting row sends the degree `n` image of the quotient to
its degree `n + 1` subobject image and then to the middle coefficient image.
A strong Serre property at the two ends of this row suffices; there is no
all-degree endpoint hypothesis or geometric exactness assumption.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u' v' w w'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive]
  (P : ObjectProperty B) [P.IsSerreClass]

/-- The fixed-degree connecting row proves the Serre property of the original
next image of the subobject from just the preceding quotient image and the
next middle image. -/
theorem rightDerived_property_succ_of_shortExact
    (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ)
    (h₃ : P ((F.rightDerived n).obj S.X₃))
    (h₂ : P ((F.rightDerived (n + 1)).obj S.X₂)) :
    P ((F.rightDerived (n + 1)).obj S.X₁) := by
  let T := DerivedCategory.Plus.ι.mapTriangle.obj
    (F.rightDerivedFunctorPlus.mapTriangle.obj hS.singleTrianglePlus)
  have hT : T ∈ distTriang (DerivedCategory B) :=
    DerivedCategory.Plus.ι.map_distinguished _
      (F.rightDerivedFunctorPlus.map_distinguished _ hS.singleTrianglePlus_distinguished)
  have hleft : P ((DerivedCategory.homologyFunctor B (n : ℤ)).obj T.obj₃) :=
    P.prop_of_iso ((F.rightDerivedSingleHomologyIso n).app S.X₃) h₃
  have hright : P ((DerivedCategory.homologyFunctor B (n + 1 : ℕ)).obj T.obj₂) :=
    P.prop_of_iso ((F.rightDerivedSingleHomologyIso (n + 1)).app S.X₂) h₂
  have hmiddle : P ((DerivedCategory.homologyFunctor B (n + 1 : ℕ)).obj T.obj₁) :=
    P.prop_X₂_of_exact
      (DerivedCategory.HomologySequence.exact₁ T hT (n : ℤ) (n + 1 : ℕ) (by omega))
      hleft hright
  exact P.prop_of_iso ((F.rightDerivedSingleHomologyIso (n + 1)).app S.X₁).symm hmiddle

end CategoryTheory.Functor
