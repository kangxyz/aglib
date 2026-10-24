/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Equivalence relations tested on the objects of a property

For parallel morphisms `p₁ p₂ : R ⟶ X` and an object `T`, `pointsRelation p₁ p₂ T` is the relation
on `T`-points of `X` whose graph is the image of `R(T) → X(T) × X(T)`: `a` and `b` are related when
`a = r ≫ p₁` and `b = r ≫ p₂` for some `r : T ⟶ R`. Mathlib's internal equivalence relations
(`CategoryTheory.EquivalenceRelation`, with joint monicity `JointlyMono₂`) give equivalence
relations on all `T`-points (`EquivalenceRelation.equivalence_pointsRelation`).

Conversely, let `P` be a property of objects and suppose that `p₁, p₂` are jointly monic. If the
relation on `T`-points is an equivalence relation for every `T` with `P T`, and `X`, `R` and
`R ×_{p₂, X, p₁} R` satisfy `P`, then `p₁, p₂` is an internal equivalence relation
(`ObjectProperty.equivalenceRelationOfPoints`, `ObjectProperty.isEquivalenceRelation_iff_points`).
Only three universal points are tested: `(𝟙, 𝟙)` on `X` for reflexivity, `(p₁, p₂)` on `R` for
symmetry, and the composable pair of the two projections on `R ×_X R` for transitivity.

Over a base `S`, `T`-points over `S` are related exactly when their underlying morphisms are
(`Over.pointsRelation_iff`), so the equivalence-relation property on points over `S` with a
property of the underlying object is the same as on points of the underlying objects
(`Over.equivalence_pointsRelation_iff`); joint monicity of the underlying morphisms gives joint
monicity over `S` (`Over.jointlyMono₂_of_left`).

Joint monicity is supplied by a monomorphism into a jointly monic pair
(`jointlyMono₂_comp_of_mono`), for example the projections of a fibre product
(`jointlyMono₂_pullback_fst_snd`).

This is the categorical core of the locally Noetherian test of a schematic equivalence relation in
`Aglib.AlgebraicGeometry.Properties.Noetherian.EquivalenceRelation`: the definition of Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §6, p. 31 quantifies over all
test schemes, while Hilbert schemes are representable only on locally Noetherian ones.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The relation on `T`-points of `X` induced by `p₁ p₂ : R ⟶ X`: `a` and `b` are related when
`(a, b)` is the image of a `T`-point of `R` under `R(T) → X(T) × X(T)`. -/
def pointsRelation {R X : C} (p₁ p₂ : R ⟶ X) (T : C) (a b : T ⟶ X) : Prop :=
  ∃ r : T ⟶ R, r ≫ p₁ = a ∧ r ≫ p₂ = b

/-- The projections of a fibre product are jointly monic. -/
instance jointlyMono₂_pullback_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    JointlyMono₂ (pullback.fst f g) (pullback.snd f g) :=
  ⟨fun _ _ _ h₁ h₂ => pullback.hom_ext h₁ h₂⟩

/-- A pair of morphisms factoring through a monomorphism into a jointly monic pair is jointly
monic. -/
theorem jointlyMono₂_comp_of_mono {R W X₁ X₂ : C} (i : R ⟶ W) [Mono i] (q₁ : W ⟶ X₁) (q₂ : W ⟶ X₂)
    [JointlyMono₂ q₁ q₂] : JointlyMono₂ (i ≫ q₁) (i ≫ q₂) :=
  ⟨fun _ f g h₁ h₂ => (cancel_mono i).mp (JointlyMono₂.right_cancellation (f ≫ i) (g ≫ i)
    (by simpa only [Category.assoc] using h₁) (by simpa only [Category.assoc] using h₂))⟩

section Points

variable {R X : C} {p₁ p₂ : R ⟶ X}

/-- Related points stay related after precomposition. -/
theorem pointsRelation.comp {T T' : C} (g : T' ⟶ T) {a b : T ⟶ X}
    (h : pointsRelation p₁ p₂ T a b) : pointsRelation p₁ p₂ T' (g ≫ a) (g ≫ b) := by
  obtain ⟨r, rfl, rfl⟩ := h
  exact ⟨g ≫ r, Category.assoc _ _ _, Category.assoc _ _ _⟩

/-- A reflexive relation relates every point with itself. -/
theorem ReflexiveRelation.pointsRelation_refl (e : ReflexiveRelation p₁ p₂) {T : C} (a : T ⟶ X) :
    pointsRelation p₁ p₂ T a a :=
  ⟨a ≫ e.r, by rw [Category.assoc, e.reflexivity₁, Category.comp_id],
    by rw [Category.assoc, e.reflexivity₂, Category.comp_id]⟩

/-- A symmetric relation on points is symmetric. -/
theorem SymmetricRelation.pointsRelation_symm (e : SymmetricRelation p₁ p₂) {T : C}
    {a b : T ⟶ X} (h : pointsRelation p₁ p₂ T a b) : pointsRelation p₁ p₂ T b a := by
  obtain ⟨r, rfl, rfl⟩ := h
  exact ⟨r ≫ e.s, by rw [Category.assoc, e.symmetry₁], by rw [Category.assoc, e.symmetry₂]⟩

/-- A transitive relation on points is transitive. -/
theorem TransitiveRelation.pointsRelation_trans (e : TransitiveRelation p₁ p₂) {T : C}
    {a b c : T ⟶ X} (hab : pointsRelation p₁ p₂ T a b) (hbc : pointsRelation p₁ p₂ T b c) :
    pointsRelation p₁ p₂ T a c := by
  obtain ⟨r, rfl, hr⟩ := hab
  obtain ⟨r', hr', rfl⟩ := hbc
  obtain ⟨l, hl₁, hl₂⟩ := PullbackCone.IsLimit.lift' e.isLimit r r' (hr.trans hr'.symm)
  refine ⟨l ≫ e.t, ?_, ?_⟩
  · rw [Category.assoc, e.transitivity₁, ← Category.assoc, hl₁]
  · rw [Category.assoc, e.transitivity₂, ← Category.assoc, hl₂]

/-- **An internal equivalence relation is an equivalence relation on `T`-points** for every
object `T`. -/
theorem EquivalenceRelation.equivalence_pointsRelation (e : EquivalenceRelation p₁ p₂) (T : C) :
    _root_.Equivalence (pointsRelation p₁ p₂ T) where
  refl a := e.toReflexiveRelation.pointsRelation_refl a
  symm h := e.toSymmetricRelation.pointsRelation_symm h
  trans hab hbc := e.toTransitiveRelation.pointsRelation_trans hab hbc

end Points

section Over

variable {S : C} {R X : Over S} {p₁ p₂ : R ⟶ X}

/-- **Points over a base**: `T`-points `a, b` of `X` over `S` are related by `p₁, p₂` if and only if
their underlying morphisms are related by `p₁.left, p₂.left`. -/
theorem Over.pointsRelation_iff {T : Over S} (a b : T ⟶ X) :
    pointsRelation p₁ p₂ T a b ↔ pointsRelation p₁.left p₂.left T.left a.left b.left := by
  constructor
  · rintro ⟨r, rfl, rfl⟩
    exact ⟨r.left, rfl, rfl⟩
  · rintro ⟨r, h₁, h₂⟩
    refine ⟨Over.homMk r ?_, Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩
    rw [← Over.w p₁, ← Category.assoc, h₁, Over.w a]

/-- Morphisms over `S` whose underlying morphisms are jointly monic are jointly monic. -/
theorem Over.jointlyMono₂_of_left [JointlyMono₂ p₁.left p₂.left] : JointlyMono₂ p₁ p₂ :=
  ⟨fun _ f g h₁ h₂ => Over.OverMorphism.ext (JointlyMono₂.right_cancellation f.left g.left
    (congrArg CommaMorphism.left h₁) (congrArg CommaMorphism.left h₂))⟩

/-- Morphisms related by `p₁.left, p₂.left` for `p₁, p₂` over `S` have the same composite to `S`. -/
theorem Over.comp_hom_eq_of_pointsRelation {T : C} {a b : T ⟶ X.left}
    (h : pointsRelation p₁.left p₂.left T a b) : a ≫ X.hom = b ≫ X.hom := by
  obtain ⟨r, rfl, rfl⟩ := h
  rw [Category.assoc, Category.assoc, Over.w p₁, Over.w p₂]

/-- **Equivalence relations on points over a base**: for `p₁, p₂ : R ⟶ X` over `S` and a property
`P` of objects of `C`, the relation on `T`-points over `S` is an equivalence relation for every `T`
over `S` with `P T.left` if and only if the relation given by `p₁.left, p₂.left` is one on
`T`-points for every `T` with `P T`. A morphism `a : T ⟶ X.left` is a point over `S` of `T` with
structure morphism `a ≫ X.hom`. -/
theorem Over.equivalence_pointsRelation_iff (P : ObjectProperty C) :
    (∀ T : Over S, P T.left → _root_.Equivalence (pointsRelation p₁ p₂ T)) ↔
      ∀ T : C, P T → _root_.Equivalence (pointsRelation p₁.left p₂.left T) := by
  constructor
  · intro h T hT
    refine ⟨fun a => ?_, fun {a b} hab => ?_, fun {a b c} hab hbc => ?_⟩
    · exact (Over.pointsRelation_iff _ _).mp
        ((h (Over.mk (a ≫ X.hom)) hT).refl (Over.homMk a rfl))
    · have hb := Over.comp_hom_eq_of_pointsRelation hab
      let T' : Over S := Over.mk (a ≫ X.hom)
      let a' : T' ⟶ X := Over.homMk a rfl
      let b' : T' ⟶ X := Over.homMk b hb.symm
      exact (Over.pointsRelation_iff b' a').mp
        ((h T' hT).symm ((Over.pointsRelation_iff a' b').mpr hab))
    · have hb := Over.comp_hom_eq_of_pointsRelation hab
      have hc := Over.comp_hom_eq_of_pointsRelation hbc
      let T' : Over S := Over.mk (a ≫ X.hom)
      let a' : T' ⟶ X := Over.homMk a rfl
      let b' : T' ⟶ X := Over.homMk b hb.symm
      let c' : T' ⟶ X := Over.homMk c (hc.symm.trans hb.symm)
      exact (Over.pointsRelation_iff a' c').mp ((h T' hT).trans
        ((Over.pointsRelation_iff a' b').mpr hab) ((Over.pointsRelation_iff b' c').mpr hbc))
  · intro h T hT
    exact ⟨fun a => (Over.pointsRelation_iff a a).mpr ((h T.left hT).refl a.left),
      fun {a b} hab => (Over.pointsRelation_iff b a).mpr
        ((h T.left hT).symm ((Over.pointsRelation_iff a b).mp hab)),
      fun {a b c} hab hbc => (Over.pointsRelation_iff a c).mpr ((h T.left hT).trans
        ((Over.pointsRelation_iff a b).mp hab) ((Over.pointsRelation_iff b c).mp hbc))⟩

end Over

namespace ObjectProperty

variable (P : ObjectProperty C) {R X : C} (p₁ p₂ : R ⟶ X)

/-- **An internal equivalence relation from points on the objects of a property**: if `p₁, p₂` are
jointly monic, the relation on `T`-points is an equivalence relation for every `T` satisfying `P`,
and `X`, `R` and `R ×_{p₂, X, p₁} R` satisfy `P`, then `p₁, p₂` is an equivalence relation. The
witnesses come from the universal points: `(𝟙, 𝟙)` on `X`, `(p₁, p₂)` on `R`, and the composable
pair of projections on `R ×_X R`. -/
def equivalenceRelationOfPoints [JointlyMono₂ p₁ p₂] [HasPullback p₂ p₁] (hX : P X) (hR : P R)
    (hRR : P (pullback p₂ p₁)) (h : ∀ T, P T → _root_.Equivalence (pointsRelation p₁ p₂ T)) :
    EquivalenceRelation p₁ p₂ where
  right_cancellation := JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂)
  r := Exists.choose ((h X hX).refl (𝟙 X))
  reflexivity₁ := (Exists.choose_spec ((h X hX).refl (𝟙 X))).1
  reflexivity₂ := (Exists.choose_spec ((h X hX).refl (𝟙 X))).2
  s := Exists.choose ((h R hR).symm ⟨𝟙 R, Category.id_comp p₁, Category.id_comp p₂⟩)
  symmetry₁ :=
    (Exists.choose_spec ((h R hR).symm ⟨𝟙 R, Category.id_comp p₁, Category.id_comp p₂⟩)).1
  symmetry₂ :=
    (Exists.choose_spec ((h R hR).symm ⟨𝟙 R, Category.id_comp p₁, Category.id_comp p₂⟩)).2
  c := PullbackCone.mk (pullback.fst p₂ p₁) (pullback.snd p₂ p₁) pullback.condition
  isLimit := pullbackIsPullback p₂ p₁
  t := Exists.choose ((h _ hRR).trans ⟨pullback.fst p₂ p₁, rfl, rfl⟩
    ⟨pullback.snd p₂ p₁, pullback.condition.symm, rfl⟩)
  transitivity₁ := (Exists.choose_spec ((h _ hRR).trans ⟨pullback.fst p₂ p₁, rfl, rfl⟩
    ⟨pullback.snd p₂ p₁, pullback.condition.symm, rfl⟩)).1
  transitivity₂ := (Exists.choose_spec ((h _ hRR).trans ⟨pullback.fst p₂ p₁, rfl, rfl⟩
    ⟨pullback.snd p₂ p₁, pullback.condition.symm, rfl⟩)).2

/-- **Equivalence relations are tested on the objects of a property**: for jointly monic
`p₁, p₂ : R ⟶ X` such that `X`, `R` and `R ×_{p₂, X, p₁} R` satisfy `P`, the pair is an internal
equivalence relation if and only if the relation on `T`-points is an equivalence relation for every
`T` satisfying `P`. -/
theorem isEquivalenceRelation_iff_points [JointlyMono₂ p₁ p₂] [HasPullback p₂ p₁] (hX : P X)
    (hR : P R) (hRR : P (pullback p₂ p₁)) :
    IsEquivalenceRelation p₁ p₂ ↔ ∀ T, P T → _root_.Equivalence (pointsRelation p₁ p₂ T) := by
  refine ⟨fun ⟨⟨e⟩⟩ T _ => e.equivalence_pointsRelation T, fun h => ?_⟩
  exact (equivalenceRelationOfPoints P p₁ p₂ hX hR hRR h).isEquivalenceRelation

end ObjectProperty

end CategoryTheory
