/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Ranges in scheme pullback squares and isomorphisms

Source: R5 revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Original declaration names, universes, maps and mathematical hypotheses are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.Range` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`449e277bf4a51f7de01c545ae15a51ccfbb01ebaf9cca8484a2e3422a5df23db`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Hom.Range

lemma range_iso_comp {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z) :
    Set.range (e.hom ≫ f) = Set.range f := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨e.hom x, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := (Scheme.homeoOfIso e).surjective y
    change e.hom x = y at hx
    exact ⟨x, by change f (e.hom x) = f y; rw [hx]⟩

end AlgebraicGeometry.Scheme.Hom.Range



namespace AlgebraicGeometry.Scheme.Pullback.Fibre

lemma preimage_range_of_overlap {A X L B : Scheme.{u}}
    (a : A ⟶ X) (i : X ⟶ B) (j : L ⟶ B) [IsOpenImmersion i]
    (h : Set.range (a ≫ i) = Set.range i ∩ Set.range j) :
    i ⁻¹' Set.range j = Set.range a := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := h.ge ⟨⟨x, rfl⟩, hx⟩
    exact ⟨z, i.isOpenEmbedding.injective hz⟩
  · rintro ⟨z, rfl⟩
    exact (h.le ⟨z, rfl⟩).2

end AlgebraicGeometry.Scheme.Pullback.Fibre

namespace AlgebraicGeometry.Scheme.Pullback.Fibre

open AlgebraicGeometry.Scheme.Hom.Range

lemma pullback_range_fst {A B C D : Scheme.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D}
    (H : IsPullback f g h i) : Set.range f = h ⁻¹' Set.range i := by
  rw [← H.isoPullback_hom_fst, AlgebraicGeometry.Scheme.Hom.Range.range_iso_comp,
      Scheme.Pullback.range_fst]

lemma pullback_range_snd {A B C D : Scheme.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D}
    (H : IsPullback f g h i) : Set.range g = i ⁻¹' Set.range h :=
  pullback_range_fst H.flip

lemma not_subset_range_of_pullback {A B C D : Scheme.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D}
    (H : IsPullback f g h i) (hf : ¬ Function.Surjective f) :
    ¬ Set.range h ⊆ Set.range i := by
  intro hs
  apply hf
  intro x
  have hx : x ∈ h ⁻¹' Set.range i := hs ⟨x, rfl⟩
  rw [← pullback_range_fst H] at hx
  exact hx

lemma nonempty_not_subset_of_disjoint {X : Type u} {A B : Set X}
    (h : Disjoint A B) (hA : A.Nonempty) : ¬ A ⊆ B := by
  intro hsub
  obtain ⟨x, hx⟩ := hA
  exact Set.disjoint_left.mp h hx (hsub hx)

lemma range_nonempty {X Y : Scheme.{u}} [Nonempty X] (f : X ⟶ Y) :
    (Set.range f).Nonempty := Set.range_nonempty f

lemma morphism_range_comp_subset {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Set.range (f ≫ g) ⊆ Set.range g := Set.range_comp_subset_range f g

lemma not_subset_postcompose {A B X Y : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (j : X ⟶ Y) (hj : Function.Injective j) (h : ¬ Set.range f ⊆ Set.range g) :
    ¬ Set.range (f ≫ j) ⊆ Set.range (g ≫ j) := by
  intro hsub
  apply h
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hsub ⟨x, rfl⟩
  exact ⟨y, hj hy⟩

end AlgebraicGeometry.Scheme.Pullback.Fibre

namespace AlgebraicGeometry.Scheme.Pullback.Transport

lemma range_eq_preimage_of_isPullback {P A B C : Scheme.{u}}
    {a : P ⟶ A} {b : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (H : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  rw [← H.isoPullback_hom_fst]
  change Set.range ((pullback.fst f g) ∘ H.isoPullback.hom) = _
  have hs : Function.Surjective H.isoPullback.hom := H.isoPullback.hom.homeomorph.surjective
  rw [hs.range_comp, Scheme.Pullback.range_fst]

end AlgebraicGeometry.Scheme.Pullback.Transport

namespace AlgebraicGeometry.Scheme.Pullback.Fibre

open AlgebraicGeometry.Scheme.Hom.Range

lemma range_snd_of_isPullback {A B C D : Scheme.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D}
    (H : IsPullback f g h i) [IsOpenImmersion h] :
    Set.range g = i ⁻¹' Set.range h := by
  rw [← H.isoPullback_hom_snd, range_iso_comp, IsOpenImmersion.range_pullbackSnd]
  rfl

lemma chart_preimage_of_overlap {A X L B : Scheme.{u}}
    (a : A ⟶ X) (i : X ⟶ B) (j : L ⟶ B) [IsOpenImmersion i]
    (h : Set.range (a ≫ i) = Set.range i ∩ Set.range j) :
    i ⁻¹' Set.range j = Set.range a := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := h.ge ⟨⟨x, rfl⟩, hx⟩
    exact ⟨z, i.isOpenEmbedding.injective hz⟩
  · rintro ⟨z, rfl⟩
    exact (h.le ⟨z, rfl⟩).2

end AlgebraicGeometry.Scheme.Pullback.Fibre

namespace AlgebraicGeometry

lemma map_mem_range_comp_iff {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hg : Function.Injective g) (z : B) :
    g z ∈ Set.range (f ≫ g) ↔ z ∈ Set.range f := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hg hq⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Pullback.Fibre

lemma cover_postcompose {A B X Y : Type*} (a : A → X) (b : B → X) (f : X → Y)
    (hf : Function.Surjective f) (h : ∀ x, x ∈ Set.range a ∨ x ∈ Set.range b) (y : Y) :
    y ∈ Set.range (f ∘ a) ∨ y ∈ Set.range (f ∘ b) := by
  obtain ⟨x, hx⟩ := hf y
  rcases h x with ⟨z, hz⟩ | ⟨z, hz⟩
  · exact Or.inl ⟨z, (congrArg f hz).trans hx⟩
  · exact Or.inr ⟨z, (congrArg f hz).trans hx⟩



end AlgebraicGeometry.Scheme.Pullback.Fibre
