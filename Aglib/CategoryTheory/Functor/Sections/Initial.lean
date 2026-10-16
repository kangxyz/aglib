/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Actual sections evaluated at an initial object

Evaluation at an initial object identifies the native sections of a
type-valued functor with its value there. The inverse is the original family
of functor maps, and coefficient naturality is literal evaluation. No limit
object or size restriction on the indexing category is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe u v w

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) {T : C} (hT : IsInitial T)

/-- Native compatible sections are determined by their value at an initial object. -/
def sectionsEquivOfIsInitial : F.sections ≃ F.obj T where
  toFun s := s.val T
  invFun x := {
    val := fun U => F.map (hT.to U) x
    property := by
      intro U V f
      change (F.map (hT.to U) ≫ F.map f) x = F.map (hT.to V) x
      rw [← F.map_comp]
      exact congrArg (fun k => F.map k x) (hT.hom_ext _ _) }
  left_inv s := by
    apply Subtype.ext
    funext U
    exact s.property (hT.to U)
  right_inv x := by
    change F.map (hT.to T) x = x
    rw [hT.hom_ext (hT.to T) (𝟙 T), F.map_id]
    rfl

/-- The actual section equivalence is evaluation. -/
theorem sectionsEquivOfIsInitial_apply (s : F.sections) :
    F.sectionsEquivOfIsInitial hT s = s.val T := rfl

/-- The inverse section is the original family of maps out of the initial object. -/
theorem sectionsEquivOfIsInitial_symm_apply (x : F.obj T) (U : C) :
    ((F.sectionsEquivOfIsInitial hT).symm x).val U = F.map (hT.to U) x := rfl

/-- The native section equivalence commutes with the original coefficient maps. -/
theorem sectionsEquivOfIsInitial_naturality {G : C ⥤ Type w} (α : F ⟶ G) (s : F.sections) :
    G.sectionsEquivOfIsInitial hT ((sectionsFunctor C).map α s) =
      α.app T (F.sectionsEquivOfIsInitial hT s) := rfl

end CategoryTheory.Functor
