/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian

/-!
# Points of projective space over a scheme and base change of the base

Let `g : T ⟶ Spec A` and `X_T = P^n_A ×_{Spec A} T` (`pullback (toSpec A ι) g`), with second
projection `X_T ⟶ T`.

* **Points.** For a ring `K` and `x : Spec K ⟶ T`, `pointRingHom g x : A →+* K` is the ring map
  with `Spec (pointRingHom g x) = x ≫ g` (`specMap_pointRingHom`), and
  `pointMap ι g x : P^n_K ⟶ X_T` has components `map (pointRingHom g x) ι` and
  `toSpec K ι ≫ x`. It exhibits `P^n_K` as the base change of `X_T ⟶ T` along `x`
  (`isPullback_pointMap`), and `map τ ι ≫ pointMap ι g x = pointMap ι g (Spec τ ≫ x)`
  (`map_comp_pointMap`). For a field `K` the pullback of a closed subscheme of `X_T` along
  `pointMap ι g x` is its fiber at `x`; over `T = Spec B` the map `pointMap ι g (𝟙 _)` is an
  isomorphism (`isIso_pointMap_id`).
* **Base change of the base.** For `f : T' ⟶ T` with `f ≫ g = g'`,
  `baseChangeMap ι g g' f h : X_{T'} ⟶ X_T` exhibits `X_{T'}` as the base change of `X_T ⟶ T`
  along `f` (`isPullback_baseChangeMap`). It is functorial (`baseChangeMap_id`,
  `baseChangeMap_comp`) and compatible with points: `pointMap ι g' x ≫ baseChangeMap ι g g' f h`
  is `pointMap ι g (x ≫ f)` (`pointMap_comp_baseChangeMap`).

The maps `affineBaseMap` and `pullbackBaseChange` of `ProjectiveSpace/BaseChange/AffineOpen` are
the instances `x = hU.fromSpec` and `g' = f ≫ g`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) {A : Type u} [CommRing A]

/-- The ring map `σ : A →+* K` of a point `x : Spec K ⟶ T` over `g : T ⟶ Spec A`, characterized by
`Spec σ = x ≫ g` (`specMap_pointRingHom`). -/
def pointRingHom {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) {K : Type u} [CommRing K]
    (x : Spec (CommRingCat.of K) ⟶ T) : A →+* K :=
  (Spec.preimage (x ≫ g)).hom

theorem specMap_pointRingHom {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) {K : Type u}
    [CommRing K] (x : Spec (CommRingCat.of K) ⟶ T) :
    Spec.map (CommRingCat.ofHom (pointRingHom g x)) = x ≫ g :=
  Spec.map_preimage _

theorem pointRingHom_congr {T T' : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
    {g' : T' ⟶ Spec (CommRingCat.of A)} {K : Type u} [CommRing K]
    {x : Spec (CommRingCat.of K) ⟶ T} {x' : Spec (CommRingCat.of K) ⟶ T'} (h : x ≫ g = x' ≫ g') :
    pointRingHom g x = pointRingHom g' x' := by
  unfold pointRingHom
  rw [h]

theorem pointRingHom_specMap_comp {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    {K L : Type u} [CommRing K] [CommRing L] (τ : K →+* L) (x : Spec (CommRingCat.of K) ⟶ T) :
    pointRingHom g (Spec.map (CommRingCat.ofHom τ) ≫ x) = τ.comp (pointRingHom g x) := by
  have h : Spec.map (CommRingCat.ofHom (τ.comp (pointRingHom g x))) =
      (Spec.map (CommRingCat.ofHom τ) ≫ x) ≫ g := by
    rw [show CommRingCat.ofHom (τ.comp (pointRingHom g x)) =
        CommRingCat.ofHom (pointRingHom g x) ≫ CommRingCat.ofHom τ from rfl, Spec.map_comp,
      specMap_pointRingHom, Category.assoc]
  change (Spec.preimage ((Spec.map (CommRingCat.ofHom τ) ≫ x) ≫ g)).hom = _
  rw [← h, Spec.preimage_map, CommRingCat.hom_ofHom]

/-- The map `P^n_K ⟶ P^n_A ×_{Spec A} T` of a point `x : Spec K ⟶ T`, with components
`ProjectiveSpace.map σ ι` and `toSpec K ι ≫ x` for `Spec σ = x ≫ g`. For a field `K` the pullback
of a closed subscheme `Z ⊆ P^n_A ×_{Spec A} T` along it is the fiber of `Z` at `x`. -/
def pointMap {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) {K : Type u} [CommRing K]
    (x : Spec (CommRingCat.of K) ⟶ T) : ProjectiveSpace K ι ⟶ pullback (toSpec A ι) g :=
  pullback.lift (map (pointRingHom g x) ι) (toSpec K ι ≫ x) (by
    rw [map_toSpec, specMap_pointRingHom, Category.assoc])

@[reassoc (attr := simp)]
theorem pointMap_fst {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) {K : Type u} [CommRing K]
    (x : Spec (CommRingCat.of K) ⟶ T) :
    pointMap ι g x ≫ pullback.fst (toSpec A ι) g = map (pointRingHom g x) ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pointMap_snd {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) {K : Type u} [CommRing K]
    (x : Spec (CommRingCat.of K) ⟶ T) :
    pointMap ι g x ≫ pullback.snd (toSpec A ι) g = toSpec K ι ≫ x :=
  pullback.lift_snd _ _ _

/-- The point map of a composite: `map τ ι ≫ pointMap ι g x = pointMap ι g (Spec τ ≫ x)`. -/
theorem map_comp_pointMap {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) {K L : Type u}
    [CommRing K] [CommRing L] (τ : K →+* L) (x : Spec (CommRingCat.of K) ⟶ T) :
    map τ ι ≫ pointMap ι g x = pointMap ι g (Spec.map (CommRingCat.ofHom τ) ≫ x) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pointMap_fst, pointMap_fst, pointRingHom_specMap_comp, map_comp]
  · rw [Category.assoc, pointMap_snd, pointMap_snd, map_toSpec_assoc]

/-- **The square `P^n_K ⟶ P^n_A ×_{Spec A} T` over a point `x : Spec K ⟶ T` is cartesian.** -/
theorem isPullback_pointMap {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) {K : Type u}
    [CommRing K] (x : Spec (CommRingCat.of K) ⟶ T) :
    IsPullback (pointMap ι g x) (toSpec K ι) (pullback.snd (toSpec A ι) g) x := by
  refine IsPullback.of_right ?_ (pointMap_snd ι g x) (IsPullback.of_hasPullback _ _)
  rw [pointMap_fst, ← specMap_pointRingHom g x]
  exact isPullback_map _ ι

/-- Over `T = Spec B`, the point map of the identity is an isomorphism
`P^n_B ≅ P^n_A ×_{Spec A} Spec B`. -/
instance isIso_pointMap_id {B : Type u} [CommRing B] (g : Spec (CommRingCat.of B) ⟶
    Spec (CommRingCat.of A)) : IsIso (pointMap ι g (𝟙 _)) :=
  (isPullback_pointMap ι g (𝟙 _)).isIso_fst_of_isIso

/-- The base-changed map `P^n_A ×_{Spec A} T' ⟶ P^n_A ×_{Spec A} T` of a morphism `f : T' ⟶ T`
over `Spec A`. -/
def baseChangeMap {T T' : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g') :
    pullback (toSpec A ι) g' ⟶ pullback (toSpec A ι) g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ f) (by
    rw [pullback.condition, Category.assoc, h])

@[reassoc (attr := simp)]
theorem baseChangeMap_fst {T T' : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g') :
    baseChangeMap ι g g' f h ≫ pullback.fst (toSpec A ι) g = pullback.fst (toSpec A ι) g' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeMap_snd {T T' : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g') :
    baseChangeMap ι g g' f h ≫ pullback.snd (toSpec A ι) g = pullback.snd (toSpec A ι) g' ≫ f :=
  pullback.lift_snd _ _ _

/-- The base-changed map is the base change of `f`: the square
`P^n_A ×_{Spec A} T' ⟶ P^n_A ×_{Spec A} T` over `T' ⟶ T` is cartesian. -/
theorem isPullback_baseChangeMap {T T' : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g') :
    IsPullback (baseChangeMap ι g g' f h) (pullback.snd (toSpec A ι) g')
      (pullback.snd (toSpec A ι) g) f := by
  refine IsPullback.of_right ?_ (baseChangeMap_snd ι g g' f h) (IsPullback.of_hasPullback _ _)
  rw [baseChangeMap_fst, h]
  exact IsPullback.of_hasPullback _ _

theorem baseChangeMap_id {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (h : 𝟙 T ≫ g = g) : baseChangeMap ι g g (𝟙 T) h = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

theorem baseChangeMap_comp {T T' T'' : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (g' : T' ⟶ Spec (CommRingCat.of A)) (g'' : T'' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T)
    (f' : T'' ⟶ T') (h : f ≫ g = g') (h' : f' ≫ g' = g'') (h'' : (f' ≫ f) ≫ g = g'') :
    baseChangeMap ι g g'' (f' ≫ f) h'' =
      baseChangeMap ι g' g'' f' h' ≫ baseChangeMap ι g g' f h := by
  apply pullback.hom_ext <;> simp

/-- The point map of the base change at a point is the point map at its image:
`pointMap ι g' x ≫ baseChangeMap ι g g' f h = pointMap ι g (x ≫ f)`. -/
theorem pointMap_comp_baseChangeMap {T T' : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g') {K : Type u} [CommRing K]
    (x : Spec (CommRingCat.of K) ⟶ T') :
    pointMap ι g' x ≫ baseChangeMap ι g g' f h = pointMap ι g (x ≫ f) := by
  have hσ : pointRingHom g' x = pointRingHom g (x ≫ f) :=
    pointRingHom_congr (by rw [Category.assoc, h])
  apply pullback.hom_ext
  · simp [hσ]
  · simp

end AlgebraicGeometry.ProjectiveSpace
