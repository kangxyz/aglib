/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction
public import Mathlib.Algebra.Homology.CochainComplexPlus

/-! # The original adjunction on bounded-below complexes -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v'

namespace CategoryTheory.Adjunction

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]

/-- The degreewise adjunction restricts to the actual bounded-below full subcategories.
Its unit and counit are the original maps of complexes. -/
def mapCochainComplexPlus (adj : L ⊣ R) :
    L.mapCochainComplexPlus ⊣ R.mapCochainComplexPlus where
  unit :=
    { app K := ObjectProperty.homMk ((adj.mapHomologicalComplex (.up ℤ)).unit.app K.obj)
      naturality {K J} f := by
        apply ObjectProperty.hom_ext
        exact (adj.mapHomologicalComplex (.up ℤ)).unit.naturality f.hom }
  counit :=
    { app K := ObjectProperty.homMk ((adj.mapHomologicalComplex (.up ℤ)).counit.app K.obj)
      naturality {K J} f := by
        apply ObjectProperty.hom_ext
        exact (adj.mapHomologicalComplex (.up ℤ)).counit.naturality f.hom }
  left_triangle_components K := by
    apply ObjectProperty.hom_ext
    exact (adj.mapHomologicalComplex (.up ℤ)).left_triangle_components K.obj
  right_triangle_components K := by
    apply ObjectProperty.hom_ext
    exact (adj.mapHomologicalComplex (.up ℤ)).right_triangle_components K.obj

end CategoryTheory.Adjunction
