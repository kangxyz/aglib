/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.Yoneda
public import Aglib.CategoryTheory.ObjectProperty.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Equivalence relations on locally Noetherian points

Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §6, p. 31, calls a
morphism `f : R ⟶ X ×_S X` a schematic equivalence relation if `R(T) → X(T) × X(T)` is injective
with image the graph of an equivalence relation for every `S`-scheme `T`; compare Stacks,
Definition 39.3.1 (Tag 022P). For the two projections `p₁ p₂ : R ⟶ X` this is Mathlib's internal
`CategoryTheory.EquivalenceRelation` (with `JointlyMono₂ p₁ p₂` for the injectivity). The Hilbert
schemes of Nitsure's Theorem 6.8 represent their functors on locally Noetherian test schemes only,
so the equivalence-relation property is tested here on `T`-points with `T` locally Noetherian. The
points are morphisms of schemes `T ⟶ X`, and `pointsRelation p₁ p₂ T` is the relation of
`Aglib.CategoryTheory.ObjectProperty.EquivalenceRelation`.

* `Scheme.isEquivalenceRelation_iff_locallyNoetherian_points`: if `p₁, p₂ : R ⟶ X` are jointly
  monic and `X`, `R` and `R ×_{p₂, X, p₁} R` are locally Noetherian, then `p₁, p₂` is an internal
  equivalence relation exactly when `pointsRelation p₁ p₂ T` is an equivalence relation for every
  locally Noetherian `T`. The test points are the universal ones on `X`, `R` and `R ×_X R`
  (`ObjectProperty.isEquivalenceRelation_iff_points`).
* `…_of_locallyOfFiniteType`: the local-Noetherianity conditions hold if `X` is locally Noetherian
  and `p₁` is locally of finite type, for example proper.
* `Scheme.isEquivalenceRelation_iff_locallyNoetherian_points_of_mono`: the same for a monomorphism
  `j : R ⟶ X ×_S X` (for example a closed immersion) and its two projections.
* `Scheme.isEquivalenceRelation_of_locallyNoetherian_points`: without monicity. For `X` locally of
  finite type over a locally Noetherian `S` and `p₁` locally of finite type, injectivity of
  `R(T) → X(T) × X(T)` and the equivalence-relation property for all locally Noetherian `T` give an
  internal equivalence relation. Joint monicity comes from
  `Scheme.mono_of_locallyNoetherian_yoneda_map_injective` applied to `R ⟶ X ×_S X`.
* `Scheme.LocallyNoetherianOver.equivalence_pointsRelation_iff`: for `p₁, p₂` over `S`, the
  equivalence-relation property on `T`-points over `S` for all `T : LocallyNoetherianOver S` is the
  same as on `T`-points of schemes for all locally Noetherian `T`
  (`Over.equivalence_pointsRelation_iff`), so the statements above apply to relations given on
  points over `S`.
* `Scheme.LocallyNoetherianOver.isEquivalenceRelation_iff`: the internal version in `Over S`. For
  jointly monic `p₁, p₂ : R ⟶ X` over `S` with `X`, `R` and `R ×_X R` locally Noetherian, `p₁, p₂`
  is an equivalence relation in `Over S` exactly when the relation on `T`-points over `S` is one for
  every `T : LocallyNoetherianOver S`; the fibre product in `Over S` is the fibre product of schemes
  (`Over.forget S` preserves pullbacks).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {R X : Scheme.{u}} (p₁ p₂ : R ⟶ X)

/-- **Equivalence relations are tested on locally Noetherian points**: for jointly monic
`p₁, p₂ : R ⟶ X` with `X`, `R` and `R ×_{p₂, X, p₁} R` locally Noetherian, `p₁, p₂` is an internal
equivalence relation if and only if `R(T) ⟶ X(T) × X(T)` has image an equivalence relation for
every locally Noetherian `T`. -/
theorem isEquivalenceRelation_iff_locallyNoetherian_points [JointlyMono₂ p₁ p₂]
    [IsLocallyNoetherian X] [IsLocallyNoetherian R] [IsLocallyNoetherian (pullback p₂ p₁)] :
    IsEquivalenceRelation p₁ p₂ ↔
      ∀ (T : Scheme.{u}) [IsLocallyNoetherian T], _root_.Equivalence (pointsRelation p₁ p₂ T) :=
  ObjectProperty.isEquivalenceRelation_iff_points (fun T : Scheme.{u} => IsLocallyNoetherian T)
    p₁ p₂ (show IsLocallyNoetherian X from inferInstance)
    (show IsLocallyNoetherian R from inferInstance)
    (show IsLocallyNoetherian (pullback p₂ p₁) from inferInstance)

/-- **Equivalence relations of finite type on locally Noetherian points**: for jointly monic
`p₁, p₂ : R ⟶ X` with `X` locally Noetherian and `p₁` locally of finite type, `p₁, p₂` is an
internal equivalence relation if and only if `R(T) ⟶ X(T) × X(T)` has image an equivalence
relation for every locally Noetherian `T`. -/
theorem isEquivalenceRelation_iff_locallyNoetherian_points_of_locallyOfFiniteType
    [JointlyMono₂ p₁ p₂] [IsLocallyNoetherian X] [LocallyOfFiniteType p₁] :
    IsEquivalenceRelation p₁ p₂ ↔
      ∀ (T : Scheme.{u}) [IsLocallyNoetherian T], _root_.Equivalence (pointsRelation p₁ p₂ T) :=
  have : IsLocallyNoetherian R := LocallyOfFiniteType.isLocallyNoetherian p₁
  isEquivalenceRelation_iff_locallyNoetherian_points p₁ p₂

/-- **Schematic equivalence relations given by a monomorphism**: let `π : X ⟶ S` with `X` locally
Noetherian, and `j : R ⟶ X ×_S X` a monomorphism (for example a closed immersion) whose first
projection `R ⟶ X` is locally of finite type. Then the two projections `R ⟶ X` form an internal
equivalence relation if and only if their image in `X(T) × X(T)` is an equivalence relation for
every locally Noetherian `T`. -/
theorem isEquivalenceRelation_iff_locallyNoetherian_points_of_mono {S : Scheme.{u}} (π : X ⟶ S)
    (j : R ⟶ pullback π π) [Mono j] [IsLocallyNoetherian X]
    [LocallyOfFiniteType (j ≫ pullback.fst π π)] :
    IsEquivalenceRelation (j ≫ pullback.fst π π) (j ≫ pullback.snd π π) ↔
      ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
        _root_.Equivalence (pointsRelation (j ≫ pullback.fst π π) (j ≫ pullback.snd π π) T) :=
  have := jointlyMono₂_comp_of_mono j (pullback.fst π π) (pullback.snd π π)
  isEquivalenceRelation_iff_locallyNoetherian_points_of_locallyOfFiniteType _ _

/-- **Schematic equivalence relations from locally Noetherian points**: let `X` be locally of
finite type over a locally Noetherian `S`, and `p₁, p₂ : R ⟶ X` over `S` with `p₁` locally of
finite type. If `R(T) → X(T) × X(T)` is injective with image an equivalence relation for every
locally Noetherian `T`, then `p₁, p₂` is an internal equivalence relation. Joint monicity comes from
the monomorphism `R ⟶ X ×_S X` (`mono_of_locallyNoetherian_yoneda_map_injective`). -/
theorem isEquivalenceRelation_of_locallyNoetherian_points {S : Scheme.{u}} (π : X ⟶ S)
    (hp : p₁ ≫ π = p₂ ≫ π) [IsLocallyNoetherian S] [LocallyOfFiniteType π]
    [LocallyOfFiniteType p₁]
    (hinj : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (r r' : T ⟶ R),
      r ≫ p₁ = r' ≫ p₁ → r ≫ p₂ = r' ≫ p₂ → r = r')
    (h : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T], _root_.Equivalence (pointsRelation p₁ p₂ T)) :
    IsEquivalenceRelation p₁ p₂ := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  obtain ⟨j, hj₁, hj₂⟩ : ∃ j : R ⟶ pullback π π,
      j ≫ pullback.fst π π = p₁ ∧ j ≫ pullback.snd π π = p₂ :=
    ⟨pullback.lift p₁ p₂ hp, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have : LocallyOfFiniteType (j ≫ pullback.fst π π) := hj₁ ▸ inferInstance
  have : LocallyOfFiniteType j := locallyOfFiniteType_of_comp j (pullback.fst π π)
  have : IsLocallyNoetherian R := LocallyOfFiniteType.isLocallyNoetherian p₁
  have : Mono j := mono_of_locallyNoetherian_yoneda_map_injective_of_locallyOfFiniteType j
    fun T _ r r' (hrr' : r ≫ j = r' ≫ j) => hinj T r r'
      (by rw [← hj₁, ← Category.assoc, hrr', Category.assoc])
      (by rw [← hj₂, ← Category.assoc, hrr', Category.assoc])
  have key := (isEquivalenceRelation_iff_locallyNoetherian_points_of_mono π j).mpr
    (by rw [hj₁, hj₂]; exact h)
  rwa [hj₁, hj₂] at key

/-- **Equivalence relations on locally Noetherian points over a base**: for `p₁, p₂ : R ⟶ X` over
`S`, the relation on `T`-points over `S` is an equivalence relation for every locally Noetherian
`T` over `S` if and only if the relation of the underlying morphisms of schemes is one on
`T`-points for every locally Noetherian scheme `T`. -/
theorem LocallyNoetherianOver.equivalence_pointsRelation_iff {S : Scheme.{u}} {R X : Over S}
    (p₁ p₂ : R ⟶ X) :
    (∀ T : LocallyNoetherianOver S, _root_.Equivalence (pointsRelation p₁ p₂ T.obj)) ↔
      ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
        _root_.Equivalence (pointsRelation p₁.left p₂.left T) := by
  have h := Over.equivalence_pointsRelation_iff (p₁ := p₁) (p₂ := p₂)
    (fun T : Scheme.{u} => IsLocallyNoetherian T)
  exact ⟨fun hp => h.mp fun T hT => hp ⟨T, hT⟩, fun hp T => h.mpr hp T.obj T.property⟩

/-- **Equivalence relations over a base are tested on locally Noetherian points**: for jointly
monic `p₁, p₂ : R ⟶ X` over `S` with `X`, `R` and `R ×_{p₂, X, p₁} R` locally Noetherian, `p₁, p₂`
is an internal equivalence relation in `Over S` if and only if `R(T) → X(T) × X(T)` has image an
equivalence relation for every locally Noetherian `T` over `S`. -/
theorem LocallyNoetherianOver.isEquivalenceRelation_iff {S : Scheme.{u}} {R X : Over S}
    (p₁ p₂ : R ⟶ X) [JointlyMono₂ p₁ p₂] [IsLocallyNoetherian X.left] [IsLocallyNoetherian R.left]
    [IsLocallyNoetherian (pullback p₂.left p₁.left)] :
    IsEquivalenceRelation p₁ p₂ ↔
      ∀ T : LocallyNoetherianOver S, _root_.Equivalence (pointsRelation p₁ p₂ T.obj) := by
  have : IsLocallyNoetherian (pullback ((Over.forget S).map p₂) ((Over.forget S).map p₁)) :=
    ‹IsLocallyNoetherian (pullback p₂.left p₁.left)›
  have hRR : IsLocallyNoetherian (pullback p₂ p₁).left :=
    isLocallyNoetherian_of_isOpenImmersion (PreservesPullback.iso (Over.forget S) p₂ p₁).hom
  rw [ObjectProperty.isEquivalenceRelation_iff_points (locallyNoetherianOver S) p₁ p₂
    (show IsLocallyNoetherian X.left from inferInstance)
    (show IsLocallyNoetherian R.left from inferInstance) hRR]
  exact ⟨fun h T => h T.obj T.property, fun h T hT => h ⟨T, hT⟩⟩

end AlgebraicGeometry.Scheme
