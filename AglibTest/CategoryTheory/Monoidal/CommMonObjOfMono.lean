/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Monoidal.CommMonObjOfMono

@[expose] public noncomputable section

open CategoryTheory

universe v u

example {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {G H : C} [MonObj G] [MonObj H] [IsCommMonObj G]
    (j : H ⟶ G) [Mono j] [IsMonHom j] : IsCommMonObj H :=
  IsCommMonObj.of_mono j
