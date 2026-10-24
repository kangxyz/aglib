/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Yoneda tests on the objects of a property

Let `P` be a property of objects of a category `C`, for example "locally Noetherian" on schemes.
The Yoneda lemma in the full subcategory of `P` tests morphisms on `T`-points with `P T` only.

* `ObjectProperty.isIso_of_yoneda_map_bijective`: a morphism `f : X ⟶ Y` with `P X` and `P Y` that
  is bijective on `T`-points for every `T` with `P T` is an isomorphism. This is Mathlib's
  `isIso_of_yoneda_map_bijective` with the test objects restricted to `P`; the proof uses only the
  test objects `X` and `Y`.
* `ObjectProperty.fst_eq_snd_of_yoneda_map_injective`,
  `ObjectProperty.isIso_diagonal_of_yoneda_map_injective` and
  `ObjectProperty.mono_of_yoneda_map_injective`: if `f : X ⟶ Y` is injective on `T`-points for
  every `T` with `P T`, and the diagonal object `X ×_Y X` satisfies `P`, then the two projections
  `X ×_Y X ⟶ X` agree, the diagonal `X ⟶ X ×_Y X` is an isomorphism, and `f` is a monomorphism.
  Only the universal pair of `T`-points of `X ×_Y X` is tested; Mathlib's
  `pullback.isIso_diagonal_iff` turns the diagonal into the monomorphism.

Sources: Stacks, Lemma 4.3.5 (Tag 001P, the Yoneda lemma) and Lemma 4.13.3 (Tag 08LR: `f` is a
monomorphism if and only if `X` is the fibre product `X ×_Y X`), applied in the full subcategory of
`P`. These are the categorical cores of the locally Noetherian Yoneda statements of
`Aglib.AlgebraicGeometry.Properties.Noetherian.Yoneda`.
-/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- **Yoneda on the objects of a property**: a morphism `f : X ⟶ Y` between objects satisfying `P`,
bijective on `T`-points for every `T` satisfying `P`, is an isomorphism. -/
theorem isIso_of_yoneda_map_bijective {X Y : C} (hX : P X) (hY : P Y) (f : X ⟶ Y)
    (hf : ∀ T, P T → Function.Bijective fun x : T ⟶ X => x ≫ f) : IsIso f := by
  obtain ⟨g, hg⟩ := (hf Y hY).2 (𝟙 Y)
  have hg' : g ≫ f = 𝟙 Y := hg
  refine ⟨g, (hf X hX).1 ?_, hg'⟩
  change (f ≫ g) ≫ f = 𝟙 X ≫ f
  rw [Category.assoc, hg', Category.comp_id, Category.id_comp]

variable {P}

/-- **Injectivity on the universal pair of points**: if `f : X ⟶ Y` is injective on `T`-points for
every `T` satisfying `P`, and `X ×_Y X` satisfies `P`, then the two projections `X ×_Y X ⟶ X`
agree. -/
theorem fst_eq_snd_of_yoneda_map_injective {X Y : C} (f : X ⟶ Y) [HasPullback f f]
    (hXX : P (pullback f f)) (hf : ∀ T, P T → Function.Injective fun x : T ⟶ X => x ≫ f) :
    pullback.fst f f = pullback.snd f f :=
  hf _ hXX (show pullback.fst f f ≫ f = pullback.snd f f ≫ f from pullback.condition)

/-- **The diagonal from points**: if `f : X ⟶ Y` is injective on `T`-points for every `T`
satisfying `P`, and `X ×_Y X` satisfies `P`, then the diagonal `X ⟶ X ×_Y X` is an isomorphism,
with inverse the first projection. -/
theorem isIso_diagonal_of_yoneda_map_injective {X Y : C} (f : X ⟶ Y) [HasPullback f f]
    (hXX : P (pullback f f)) (hf : ∀ T, P T → Function.Injective fun x : T ⟶ X => x ≫ f) :
    IsIso (pullback.diagonal f) := by
  have h := fst_eq_snd_of_yoneda_map_injective f hXX hf
  refine ⟨pullback.fst f f, pullback.diagonal_fst f, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.id_comp, h]

/-- **Monomorphisms from injectivity on points**, through the diagonal: if `f : X ⟶ Y` is
injective on `T`-points for every `T` satisfying `P`, and `X ×_Y X` satisfies `P`, then `f` is a
monomorphism. -/
theorem mono_of_yoneda_map_injective {X Y : C} (f : X ⟶ Y) [HasPullback f f]
    (hXX : P (pullback f f)) (hf : ∀ T, P T → Function.Injective fun x : T ⟶ X => x ≫ f) :
    Mono f :=
  (pullback.isIso_diagonal_iff f).mp (isIso_diagonal_of_yoneda_map_injective f hXX hf)

end CategoryTheory.ObjectProperty
