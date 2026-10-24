/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InverseLimit.Elements
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Entire strict-predecessor diagrams

The indexing category contains every strict predecessor. In particular the
comparison below is not a selected pairwise transition map.
-/

@[expose] public noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex.InverseLimit

variable {J : Type w} [PartialOrder J]

/-- The native inclusion of the strict initial segment. -/
def predecessorInclusion (i : J) : Set.Iio i ⥤ J :=
  (show Monotone (fun j : Set.Iio i => (j : J)) from fun _ _ h => h).functor

variable (F : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)

/-- Restriction to all strict predecessors. -/
def predecessors (i : J) : (Set.Iio i)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (predecessorInclusion i).op ⋙ F

/-- The actual stage cone on the complete predecessor diagram. -/
def predecessorCone (i : J) : Cone (predecessors F i) where
  pt := F.obj (op i)
  π :=
    { app := fun j => F.map (homOfLE j.unop.property.le).op
      naturality := fun j k f => by
        dsimp [predecessors, predecessorInclusion]
        rw [Category.id_comp, ← F.map_comp]
        congr 1 }

/-- The actual map to the entire predecessor limit. -/
def predecessorComparison (i : J) [HasLimit (predecessors F i)] :
    F.obj (op i) ⟶ limit (predecessors F i) :=
  limit.lift _ (predecessorCone F i)

@[reassoc (attr := simp)]
lemma predecessorComparison_π (i : J) [HasLimit (predecessors F i)]
    (j : (Set.Iio i)ᵒᵖ) :
    predecessorComparison F i ≫ limit.π (predecessors F i) j =
      F.map (homOfLE j.unop.property.le).op :=
  limit.lift_π _ _

end CochainComplex.InverseLimit
