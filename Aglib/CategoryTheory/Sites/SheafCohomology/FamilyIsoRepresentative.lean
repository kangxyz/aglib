/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.IsoRepresentative

/-! # Whole-family original class representatives through coefficient isomorphisms

The dependent index choice, inverse representative and complete return equation
are constructed together while the sites, coefficients and return functions
are variables. Concrete applications supply their actual family of isomorphisms
and actual prior representatives without eliminating the geometric existential.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Sheaf

universe u v w e t a

/-- Transport the entire family of original representatives through actual
coefficient isomorphisms, including its dependent index choice. -/
theorem H.exists_family_iso_representative_return
    {ι : Type t} {C : ι → Type u} [∀ i, Category.{v} (C i)]
    (J : ∀ i, GrothendieckTopology (C i))
    [∀ i, HasSheafify (J i) AddCommGrpCat.{w}]
    [∀ i, HasExt.{e} (Sheaf (J i) AddCommGrpCat.{w})]
    {M N : ∀ i, Sheaf (J i) AddCommGrpCat.{w}}
    (E : ∀ i, M i ≅ N i) (q : ℕ)
    {A : Type a} (r : ∀ i, H.{e} (N i) q → A) (a : A)
    (h : ∃ (i : ι) (z : H.{e} (N i) q), r i z = a) :
    ∃ (i : ι) (x : H.{e} (M i) q), r i (H.map (E i).hom q x) = a := by
  obtain ⟨i, z, hz⟩ := h
  refine ⟨i, ?_⟩
  exact H.exists_iso_representative_return (E i).hom q (r i) a z hz

end CategoryTheory.Sheaf
