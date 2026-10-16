/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Short exactness through full subcategories

A natural isomorphism from an additive functor followed by a full-subcategory inclusion
to an additive functor transfers short exactness of the mapped short complex. The result
retains the two successive maps through the subcategory and its inclusion.
-/

@[expose] public section

universe uC vC uD vD

namespace CategoryTheory.ShortComplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Transfer short exactness along a natural isomorphism after a full-subcategory inclusion. -/
theorem shortExact_map_of_comp_iso
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Preadditive C] [Preadditive D]
    (P : ObjectProperty D) (G : C ⥤ P.FullSubcategory) (F : C ⥤ D)
    [G.Additive] [F.Additive] (e : G ⋙ P.ι ≅ F)
    (S : ShortComplex C) (hS : (S.map F).ShortExact) :
    ((S.map G).map P.ι).ShortExact := by
  have h : (S.map (G ⋙ P.ι)).ShortExact :=
    ShortComplex.shortExact_of_iso (S.mapNatIso e.symm) hS
  simpa only [ShortComplex.map_comp] using h

end CategoryTheory.ShortComplex
