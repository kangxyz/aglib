/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.FamilyIsoRepresentative

/-! # Whole natural-isomorphism families and original representatives

All functor carriers, natural isomorphisms, component maps and cohomology
realizations remain variables throughout the complete representative proof.
-/

@[expose] public noncomputable section
namespace CategoryTheory.Sheaf

universe u v w e t a d h

/-- Construct representatives through whole original natural isomorphisms,
before evaluating any concrete functor or object. -/
theorem H.exists_family_naturalIso_representative_return
    {ι : Type t} {C : ι → Type u} [∀ i, Category.{v} (C i)]
    (J : ∀ i, GrothendieckTopology (C i))
    [∀ i, HasSheafify (J i) AddCommGrpCat.{w}]
    [∀ i, HasExt.{e} (Sheaf (J i) AddCommGrpCat.{w})]
    {D : Type d} [Category.{h} D]
    {F G : ∀ i, D ⥤ Sheaf (J i) AddCommGrpCat.{w}}
    (E : ∀ i, F i ≅ G i) (M : D) (q : ℕ)
    {A : Type a} (r : ∀ i, H.{e} ((G i).obj M) q → A) (a : A)
    (ha : ∃ (i : ι) (z : H.{e} ((G i).obj M) q), r i z = a) :
    ∃ (i : ι) (x : H.{e} ((F i).obj M) q),
      r i (H.map ((E i).hom.app M) q x) = a :=
  H.exists_family_iso_representative_return J (fun i => (E i).app M) q r a ha

end CategoryTheory.Sheaf
