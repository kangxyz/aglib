/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Comparison
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Slice cohomology at the standard large coefficient universe

For a site with objects in universe `u` and morphisms in `v`, coefficients in
`max u v` admit the actual sheafifications and standard Ext groups needed
by the slice comparison. No size/existence premise is left to a consumer.
This includes small-etale sites with coefficients one universe above schemes.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.SliceCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)

local instance : HasSheafify J AddCommGrpCat.{max u v} := by infer_instance
local instance : HasSheafify (J.over U) AddCommGrpCat.{max u v} := by infer_instance

local instance : HasExt.{max (u + 1) (v + 1)}
    (Sheaf J AddCommGrpCat.{max u v}) := HasExt.standard _
local instance : HasExt.{max (u + 1) (v + 1)}
    (Sheaf (J.over U) AddCommGrpCat.{max u v}) := HasExt.standard _

/-- The actual large-universe comparison with its standard Ext sizes discharged. -/
def largeStandardSliceComparison (F : Sheaf J AddCommGrpCat.{max u v}) (n : ℕ) :
    LargeCohomology.H J F n U ≃+ Sheaf.H (F.over U) n :=
  sliceComparison J U F n

end CategoryTheory.Sheaf.SliceCohomology
