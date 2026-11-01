/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.FlatKanExtension
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.RaisedInjectives
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Functors

/-! # Exact native opens pullback with an independent abelian value universe

The complete generic site construction proves exactness of the original
functor. The results are theorems, not overlapping instances for the existing
same-value topological pullback API.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat.Sheaf

universe u v

local instance opensAbelianSheafify (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} :=
  CategoryTheory.Sheaf.LargeCohomology.hasSheafifyRaised.{u, u, v} _

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms

/-- Native inverse image on opens preserves finite limits at every sufficiently
large additive value universe. -/
theorem opensAbelianPullback_preservesFiniteLimits :
    PreservesFiniteLimits ((Opens.map f).sheafPullback AddCommGrpCat.{max u v}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) := by
  let : RepresentablyFlat (Opens.map f) := flat_of_preservesFiniteLimits _
  let : ∀ T : (Opens X)ᵒᵖ, IsFiltered (CostructuredArrow (Opens.map f).op T) := fun T =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (Opens.map f) (Opposite.unop T))
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v, max u v} _
  let : PreservesFiniteLimits
      ((Opens.map f).op.lan : ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤
        (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
    Functor.lan_preservesFiniteLimits_of_flat_of_shapes AddCommGrpCat.{max u v} (Opens.map f)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (Opens.map f) AddCommGrpCat.{max u v}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The same original functor is additive, with no replacement pullback model. -/
theorem opensAbelianPullback_additive :
    ((Opens.map f).sheafPullback AddCommGrpCat.{max u v}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).Additive := by
  let := opensAbelianPullback_preservesFiniteLimits.{u, v} f
  exact Functor.additive_of_preserves_binary_products _

end TopCat.Sheaf
