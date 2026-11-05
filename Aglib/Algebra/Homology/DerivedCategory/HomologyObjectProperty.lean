/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ObjectProperty

/-! # Weak-Serre properties of the original homology triangle

All three producers use five consecutive terms of the original homology exact
sequence. Only kernels and cokernels between objects already known to satisfy
the property are used. There is no arbitrary-subobject closure assumption.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CategoryTheory.ObjectProperty
universe u v w
variable {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    (P : ObjectProperty B) [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (T : Triangle (DerivedCategory B)) (hT : T ∈ distTriang (DerivedCategory B))

include hT

/-- The middle vertex has the all-degree property if the other two do. -/
theorem homology_middle_of_distinguished
    (hleft : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor B i).obj T.obj₁))
    (hright : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor B i).obj T.obj₃)) (i : ℤ) :
    P ((DerivedCategory.homologyFunctor B i).obj T.obj₂) :=
    P.prop_middle_of_exact_five
      (DerivedCategory.HomologySequence.δ T (i - 1) i (by omega))
      ((DerivedCategory.homologyFunctor B i).map T.mor₁)
      ((DerivedCategory.homologyFunctor B i).map T.mor₂)
      (DerivedCategory.HomologySequence.δ T i (i + 1) rfl)
      (DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i (by omega))
      (DerivedCategory.HomologySequence.exact₂ T hT i)
      (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl)
      (hright (i - 1)) (hleft i) (hright i) (hleft (i + 1))

/-- The left vertex has the all-degree property if the other two do. -/
theorem homology_left_of_distinguished
    (hmiddle : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor B i).obj T.obj₂))
    (hright : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor B i).obj T.obj₃)) (i : ℤ) :
    P ((DerivedCategory.homologyFunctor B i).obj T.obj₁) :=
    P.prop_middle_of_exact_five
      ((DerivedCategory.homologyFunctor B (i - 1)).map T.mor₂)
      (DerivedCategory.HomologySequence.δ T (i - 1) i (by omega))
      ((DerivedCategory.homologyFunctor B i).map T.mor₁)
      ((DerivedCategory.homologyFunctor B i).map T.mor₂)
      (DerivedCategory.HomologySequence.exact₃ T hT (i - 1) i (by omega))
      (DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i (by omega))
      (DerivedCategory.HomologySequence.exact₂ T hT i)
      (hmiddle (i - 1)) (hright (i - 1)) (hmiddle i) (hright i)

/-- The right vertex has the all-degree property if the other two do. -/
theorem homology_right_of_distinguished
    (hleft : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor B i).obj T.obj₁))
    (hmiddle : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor B i).obj T.obj₂)) (i : ℤ) :
    P ((DerivedCategory.homologyFunctor B i).obj T.obj₃) :=
    P.prop_middle_of_exact_five
      ((DerivedCategory.homologyFunctor B i).map T.mor₁)
      ((DerivedCategory.homologyFunctor B i).map T.mor₂)
      (DerivedCategory.HomologySequence.δ T i (i + 1) rfl)
      ((DerivedCategory.homologyFunctor B (i + 1)).map T.mor₁)
      (DerivedCategory.HomologySequence.exact₂ T hT i)
      (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl)
      (DerivedCategory.HomologySequence.exact₁ T hT i (i + 1) rfl)
      (hleft i) (hmiddle i) (hleft (i + 1)) (hmiddle (i + 1))

end CategoryTheory.ObjectProperty
