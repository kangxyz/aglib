/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions on homological complexes

An additive adjunction between abelian categories acts on the actual homological
complexes of every supplied shape. Its unit and counit have the original
degreewise components; no homotopy or derived category is introduced here.

Source: `Quillen/Algebra/Homology/Adjunction.lean` at frozen dirty Quillen
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `1b633acd4a4a8f7639b1946acdfd90261736255b077c863c324777b87b16ac60`.
Selected source lines: 38–60.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]

/-- The original adjunction acts degreewise, retaining its literal unit and counit. -/
def mapHomologicalComplex {ι : Type w} (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c where
  unit := {
    app K := {
      f n := adj.unit.app (K.X n)
      comm' p q _ := (adj.unit.naturality (K.d p q)).symm }
    naturality {K L} f := by
      ext n : 1
      exact adj.unit.naturality (f.f n) }
  counit := {
    app K := {
      f n := adj.counit.app (K.X n)
      comm' p q _ := (adj.counit.naturality (K.d p q)).symm }
    naturality {K L} f := by
      ext n : 1
      exact adj.counit.naturality (f.f n) }
  left_triangle_components K := by
    ext n : 1
    exact adj.left_triangle_components (K.X n)
  right_triangle_components K := by
    ext n : 1
    exact adj.right_triangle_components (K.X n)

end CategoryTheory.Adjunction
