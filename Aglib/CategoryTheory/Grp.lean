/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Explicit underlying-object composition for morphisms of internal groups.

Source: `lean/R5Lab/Aglib/CategoryTheory/Grp.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `f14c91206203a4b8f38291ccf79ad74975fd901d308d9d34995c01bd946714e7`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

namespace CategoryTheory.Grp
universe u v

/-- Precomposing a group-morphism composite, with explicit underlying objects. -/
theorem comp_hom_hom_precomp
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]
    {G H K : Grp C} {P : C}
    (f : G ⟶ H) (g : H ⟶ K) (x : P ⟶ G.X) :
    @Eq (P ⟶ K.X)
      (CategoryStruct.comp (X := P) (Y := G.X) (Z := K.X) x (f ≫ g).hom.hom)
      (CategoryStruct.comp (X := P) (Y := H.X) (Z := K.X)
        (CategoryStruct.comp (X := P) (Y := G.X) (Z := H.X) x f.hom.hom)
        g.hom.hom) := by
  change @Eq (P ⟶ K.X)
    (CategoryStruct.comp (X := P) (Y := G.X) (Z := K.X) x
      (CategoryStruct.comp (X := G.X) (Y := H.X) (Z := K.X) f.hom.hom g.hom.hom))
    (CategoryStruct.comp (X := P) (Y := H.X) (Z := K.X)
      (CategoryStruct.comp (X := P) (Y := G.X) (Z := H.X) x f.hom.hom)
      g.hom.hom)
  exact (Category.assoc (W := P) (X := G.X) (Y := H.X) (Z := K.X)
    x f.hom.hom g.hom.hom).symm

end CategoryTheory.Grp
