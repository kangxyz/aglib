/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.NatTrans.UnitInsertion

/-! # Paste the original unit and augmentation across a comparison

The bridge and its whole span are constructed while all categories and functors
remain variable. The geometric input is the unit equation for the given original
comparison and mate; the augmentation equations follow from naturality.
-/

@[expose] public section

namespace CategoryTheory.NatTrans

universe uC vC uD vD uE vE uF vF

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] {F : Type uF} [Category.{vF} F]

/-- The original mate followed by restriction of the original augmentation. -/
def unitInsertionBridge (L : C ⥤ D) (S : C ⥤ E) (L' : E ⥤ F)
    (T : D ⥤ F) (G : D ⥤ D) (β : S ⋙ L' ⟶ L ⋙ T) (δ : 𝟭 D ⟶ G) :
    S ⋙ L' ⟶ L ⋙ G ⋙ T :=
  β ≫ Functor.whiskerLeft L (Functor.whiskerRight δ T)

/-- The bridge keeps the two original component arrows. -/
theorem unitInsertionBridge_app (L : C ⥤ D) (S : C ⥤ E) (L' : E ⥤ F)
    (T : D ⥤ F) (G : D ⥤ D) (β : S ⋙ L' ⟶ L ⋙ T) (δ : 𝟭 D ⟶ G) (K : C) :
    (unitInsertionBridge L S L' T G β δ).app K =
      β.app K ≫ T.map (δ.app (L.obj K)) := rfl

variable (L : C ⥤ D) (R : D ⥤ C) (S : C ⥤ E) (T : D ⥤ F)
  (L' : E ⥤ F) (R' : F ⥤ E) (G : D ⥤ D) (H : F ⥤ F)
  (η : 𝟭 C ⟶ L ⋙ R) (η' : 𝟭 E ⟶ L' ⋙ R')
  (δ : 𝟭 D ⟶ G) (ε : 𝟭 F ⟶ H)
  (α : R ⋙ S ⟶ T ⋙ R') (β : S ⋙ L' ⟶ L ⋙ T)

/-- The whole first square follows from the original unit equation and comparison naturality. -/
theorem unitInsertion_first_square
    (hη : ∀ K : C, S.map (η.app K) ≫ α.app (L.obj K) =
      η'.app (S.obj K) ≫ R'.map (β.app K)) :
    (Functor.whiskerRight η S ≫
      Functor.whiskerLeft L (Functor.whiskerRight δ (R ⋙ S))) ≫
        Functor.whiskerLeft (L ⋙ G) α =
      Functor.whiskerLeft S η' ≫
        Functor.whiskerRight (unitInsertionBridge L S L' T G β δ) R' := by
  apply NatTrans.ext
  funext K
  change (S.map (η.app K) ≫ S.map (R.map (δ.app (L.obj K)))) ≫
      α.app (G.obj (L.obj K)) =
    η'.app (S.obj K) ≫ R'.map (β.app K ≫ T.map (δ.app (L.obj K)))
  have hn := α.naturality (δ.app (L.obj K))
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  rw [Category.assoc, hn, ← Category.assoc, hη K, R'.map_comp, Category.assoc]

/-- The whole second square is naturality of the original target augmentation at the bridge. -/
theorem unitInsertion_second_square :
    Functor.whiskerRight (unitInsertionBridge L S L' T G β δ) R' ≫
      Functor.whiskerLeft (L ⋙ G ⋙ T) (Functor.whiskerRight ε R') =
    Functor.whiskerLeft (S ⋙ L') (Functor.whiskerRight ε R') ≫
      Functor.whiskerRight (Functor.whiskerRight
        (unitInsertionBridge L S L' T G β δ) H) R' := by
  apply NatTrans.ext
  funext K
  change R'.map ((unitInsertionBridge L S L' T G β δ).app K) ≫
      R'.map (ε.app (T.obj (G.obj (L.obj K)))) =
    R'.map (ε.app (L'.obj (S.obj K))) ≫
      R'.map (H.map ((unitInsertionBridge L S L' T G β δ).app K))
  have hn := ε.naturality ((unitInsertionBridge L S L' T G β δ).app K)
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj] at hn
  simpa only [Functor.map_comp] using congrArg R'.map hn

/-- The complete factorized span, proved before choosing an input object or degree. -/
theorem unitInsertion_span_factorized
    (hη : ∀ K : C, S.map (η.app K) ≫ α.app (L.obj K) =
      η'.app (S.obj K) ≫ R'.map (β.app K)) :
    (Functor.whiskerRight η S ≫
      Functor.whiskerLeft L (Functor.whiskerRight δ (R ⋙ S))) ≫
      Functor.whiskerLeft (L ⋙ G) α ≫
      Functor.whiskerLeft (L ⋙ G ⋙ T) (Functor.whiskerRight ε R') =
    Functor.whiskerLeft S (unitInsertion L' R' H η' ε) ≫
      Functor.whiskerRight (Functor.whiskerRight
        (unitInsertionBridge L S L' T G β δ) H) R' := by
  rw [← Category.assoc, unitInsertion_first_square L R S T L' R' G η η' δ α β hη,
    Category.assoc, unitInsertion_second_square L S T L' R' G H δ ε β,
    ← Category.assoc]
  rfl

/-- The same span uses the unchanged original inserted unit as its first arrow. -/
theorem unitInsertion_span
    (hη : ∀ K : C, S.map (η.app K) ≫ α.app (L.obj K) =
      η'.app (S.obj K) ≫ R'.map (β.app K)) :
    Functor.whiskerRight (unitInsertion L R G η δ) S ≫
      Functor.whiskerLeft (L ⋙ G) α ≫
      Functor.whiskerLeft (L ⋙ G ⋙ T) (Functor.whiskerRight ε R') =
    Functor.whiskerLeft S (unitInsertion L' R' H η' ε) ≫
      Functor.whiskerRight (Functor.whiskerRight
        (unitInsertionBridge L S L' T G β δ) H) R' := by
  have hu : Functor.whiskerRight (unitInsertion L R G η δ) S =
      Functor.whiskerRight η S ≫
        Functor.whiskerLeft L (Functor.whiskerRight δ (R ⋙ S)) := by
    apply NatTrans.ext
    funext K
    exact S.map_comp (η.app K) (R.map (δ.app (L.obj K)))
  rw [hu]
  exact unitInsertion_span_factorized L R S T L' R' G H η η' δ ε α β hη

/-- Evaluate the whole first square while the original functors remain variable. -/
theorem unitInsertion_first_square_app
    (hη : ∀ K : C, S.map (η.app K) ≫ α.app (L.obj K) =
      η'.app (S.obj K) ≫ R'.map (β.app K)) (K : C) :
    (S.map (η.app K) ≫ (R ⋙ S).map (δ.app (L.obj K))) ≫
      α.app (G.obj (L.obj K)) =
    η'.app (S.obj K) ≫ R'.map ((unitInsertionBridge L S L' T G β δ).app K) := by
  have hw := unitInsertion_first_square L R S T L' R' G η η' δ α β hη
  have he := congrArg (fun γ => γ.app K) hw
  exact he

/-- Evaluate the whole second square while the original bridge and augmentation remain variable. -/
theorem unitInsertion_second_square_app (K : C) :
    R'.map ((unitInsertionBridge L S L' T G β δ).app K) ≫
      R'.map (ε.app (T.obj (G.obj (L.obj K)))) =
    R'.map (ε.app (L'.obj (S.obj K))) ≫
      R'.map (H.map ((unitInsertionBridge L S L' T G β δ).app K)) := by
  have hw := unitInsertion_second_square L S T L' R' G H δ ε β
  have he := congrArg (fun γ => γ.app K) hw
  exact he

/-- Evaluate the complete factorized span before specializing its categories or functors. -/
theorem unitInsertion_span_factorized_app
    (hη : ∀ K : C, S.map (η.app K) ≫ α.app (L.obj K) =
      η'.app (S.obj K) ≫ R'.map (β.app K)) (K : C) :
    (S.map (η.app K) ≫ (R ⋙ S).map (δ.app (L.obj K))) ≫
      α.app (G.obj (L.obj K)) ≫ R'.map (ε.app (T.obj (G.obj (L.obj K)))) =
    (η'.app (S.obj K) ≫ R'.map (ε.app (L'.obj (S.obj K)))) ≫
      R'.map (H.map ((unitInsertionBridge L S L' T G β δ).app K)) := by
  have hw := unitInsertion_span_factorized L R S T L' R' G H η η' δ ε α β hη
  have he := congrArg (fun γ => γ.app K) hw
  exact he

section Point

universe uZ vZ
variable {Z : Type uZ} [Category.{vZ} Z]

/-- Paste the original unit equation with comparison naturality at one actual arrow. -/
theorem unitInsertion_first_square_point
    (F₁ : D ⥤ E) (T : D ⥤ F) (R' : F ⥤ E) (α : F₁ ⟶ T ⋙ R')
    {A B : D} {X : E} {Y : F} (δ : A ⟶ B)
    (u : X ⟶ F₁.obj A) (v : X ⟶ R'.obj Y) (β : Y ⟶ T.obj A)
    (hunit : u ≫ α.app A = v ≫ R'.map β) :
    (u ≫ F₁.map δ) ≫ α.app B = v ≫ R'.map (β ≫ T.map δ) := by
  have hn := α.naturality δ
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, hn, ← Category.assoc, hunit, R'.map_comp, Category.assoc]

/-- Evaluate the complete first square through an actual functor while all data remain variable. -/
theorem unitInsertion_first_square_point_map
    (F₁ : D ⥤ E) (T : D ⥤ F) (R' : F ⥤ E) (α : F₁ ⟶ T ⋙ R')
    {A B : D} {X : E} {Y : F} (δ : A ⟶ B)
    (u : X ⟶ F₁.obj A) (v : X ⟶ R'.obj Y) (β : Y ⟶ T.obj A)
    (hunit : u ≫ α.app A = v ≫ R'.map β) (P : E ⥤ Z) :
    (P.map u ≫ P.map (F₁.map δ)) ≫ P.map (α.app B) =
      P.map v ≫ P.map (R'.map (β ≫ T.map δ)) := by
  have hw := unitInsertion_first_square_point F₁ T R' α δ u v β hunit
  have he := congrArg P.map hw
  simpa only [Functor.map_comp] using he

/-- The complete span at the original arrows; the bridge equation is its original value law. -/
theorem unitInsertion_span_point
    (F₁ : D ⥤ E) (T : D ⥤ F) (R' : F ⥤ E) (α : F₁ ⟶ T ⋙ R')
    (H : F ⥤ F) (ε : 𝟭 F ⟶ H)
    {A B : D} {X : E} {Y : F} (δ : A ⟶ B)
    (u : X ⟶ F₁.obj A) (v : X ⟶ R'.obj Y) (β : Y ⟶ T.obj A)
    (hunit : u ≫ α.app A = v ≫ R'.map β)
    (s : Y ⟶ T.obj B) (hs : s = β ≫ T.map δ) :
    (u ≫ F₁.map δ) ≫ α.app B ≫ R'.map (ε.app (T.obj B)) =
      (v ≫ R'.map (ε.app Y)) ≫ R'.map (H.map s) := by
  subst s
  have hfirst := unitInsertion_first_square_point F₁ T R' α δ u v β hunit
  have hn := ε.naturality (β ≫ T.map δ)
  dsimp only [Functor.id_obj, Functor.id_map] at hn
  have hsecond : R'.map (β ≫ T.map δ) ≫ R'.map (ε.app (T.obj B)) =
      R'.map (ε.app Y) ≫ R'.map (H.map (β ≫ T.map δ)) := by
    simpa only [Functor.map_comp] using congrArg R'.map hn
  rw [← Category.assoc, hfirst, Category.assoc, hsecond, ← Category.assoc]

/-- Evaluate the whole pointwise span before supplying its native category realization. -/
theorem unitInsertion_span_point_map
    (F₁ : D ⥤ E) (T : D ⥤ F) (R' : F ⥤ E) (α : F₁ ⟶ T ⋙ R')
    (H : F ⥤ F) (ε : 𝟭 F ⟶ H)
    {A B : D} {X : E} {Y : F} (δ : A ⟶ B)
    (u : X ⟶ F₁.obj A) (v : X ⟶ R'.obj Y) (β : Y ⟶ T.obj A)
    (hunit : u ≫ α.app A = v ≫ R'.map β)
    (s : Y ⟶ T.obj B) (hs : s = β ≫ T.map δ) (P : E ⥤ Z) :
    (P.map u ≫ P.map (F₁.map δ)) ≫ P.map (α.app B) ≫
      P.map (R'.map (ε.app (T.obj B))) =
    (P.map v ≫ P.map (R'.map (ε.app Y))) ≫ P.map (R'.map (H.map s)) := by
  have hw := unitInsertion_span_point F₁ T R' α H ε δ u v β hunit s hs
  have he := congrArg P.map hw
  simpa only [Functor.map_comp] using he

/-- Evaluate a proved span at its actual original factors, with the displayed associations. -/
theorem unitInsertion_map_span_eq (P : E ⥤ Z)
    {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ : E}
    (u : X₀ ⟶ X₁) (p : X₁ ⟶ X₂) (q : X₂ ⟶ X₃) (r : X₃ ⟶ X₄)
    (v : X₀ ⟶ Y₁) (w : Y₁ ⟶ Y₂) (s : Y₂ ⟶ X₄)
    (h : (u ≫ p) ≫ q ≫ r = (v ≫ w) ≫ s) :
    (P.map u ≫ P.map p) ≫ P.map q ≫ P.map r =
      (P.map v ≫ P.map w) ≫ P.map s := by
  have he := congrArg P.map h
  simpa only [Functor.map_comp] using he

end Point

end CategoryTheory.NatTrans
