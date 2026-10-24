/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.Yoneda
public import Aglib.CategoryTheory.ObjectProperty.EquivalenceRelation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Hilbert data for the quotient by a flat proper equivalence relation

Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, proves Theorem 6.8
(pp. 33–35; the quotient of a quasi-projective `X` by a schematic equivalence relation
`f : R ⟶ X ×_S X` with proper flat projections) through the Hilbert scheme of `X`: the relation
`R`, a family over `X` through its second projection, has a classifying morphism `φ : X ⟶ H` to a
finite union `H` of Hilbert schemes of `X`, with `φ^* D = R` for the universal family
`D ⊆ X ×_S H` (p. 33). This file isolates what the rest of the proof uses of `(H, D, φ)`.

* `QuotientHilbertDatum πZ j`, for `πZ : Z ⟶ S` and `j : R ⟶ Z ×_S Z`: a scheme `H` over `S`, a
  closed subscheme `D ⊆ Z ×_S H` (an ideal sheaf, `Z` the first factor) that is flat, proper and
  surjective over `H`, and `φ : Z ⟶ H` over `S` with `D.comap (𝟙 × φ) = ker j` (Nitsure's
  `φ^* D = R`). Its last field is the injectivity half of the representability of the Hilbert
  functor: two `T`-points `a, b` of `H` over `S`, `T` locally Noetherian, with the same pulled-back
  family `D.comap (𝟙 × a) = D.comap (𝟙 × b)` on `Z ×_S T` are equal.
* `QuotientHilbertDatum.familyProj`: the projection `p : D ⟶ H`, flat, proper and surjective.
* **Membership** (Nitsure p. 33): for `x : T ⟶ Z` and `V : T ⟶ H` over `g : T ⟶ S`, Nitsure's
  `x ∈ V` means that `(x, 𝟙_T) : T ⟶ Z ×_S T` factors through the pulled-back family
  `D.comap (𝟙 × V)`; this holds exactly when `(x, V) : T ⟶ Z ×_S H` factors through `D`, so the
  `T`-points of `D` are the pairs `(x, V)` with `x ∈ V`
  (`QuotientHilbertDatum.exists_lift_comap_iff_exists_lift`).
* **The first equivalence of `(***)`** (p. 34): for `x, y : T ⟶ Z`, `(x, y) ∈ R(T)` if and only if
  `x ∈ φ(y)`, that is, `(x, φ ∘ y)` factors through `D`
  (`QuotientHilbertDatum.exists_lift_subschemeι_iff_pointsRelation`). Here `(x, y) ∈ R(T)` is
  `pointsRelation (j ≫ pr₁) (j ≫ pr₂) T x y`; `j` is a closed immersion. This holds for every
  scheme `T`; Nitsure derives it from `y^* R = φ(y)`, and here it is the universal property of the
  pullback `D.comap (𝟙 × φ) = ker j` along `(x, y) ≫ (𝟙 × φ) = (x, φ ∘ y)`. Nitsure's form,
  `(x, 𝟙_T)` factoring through `φ(y) ⊆ Z ×_S T`, is
  `QuotientHilbertDatum.pointsRelation_iff_exists_lift_comap`, and `y^* R = φ(y)` is
  `QuotientHilbertDatum.ker_comap_eq_comap`.

Families over `H` are pulled back to `T` along `𝟙 × a : Z ×_S T ⟶ Z ×_S H` for `a : T ⟶ H` over
`g : T ⟶ S`, that is, `pullback.map πZ g πZ πH (𝟙 Z) a (𝟙 S)`. The base `S` is arbitrary here;
Nitsure's `S` is Noetherian, and the Hilbert scheme represents its functor on locally Noetherian
test schemes only (§1, p. 2), which is why the injectivity field is stated for locally Noetherian
`T`. The categorical statement behind the first equivalence, that `(x, y)` factors through
`j : R ⟶ X ×_S X` exactly when `x, y` are related by `(j ≫ pr₁, j ≫ pr₂)`, is
`CategoryTheory.pointsRelation_comp_fst_comp_snd_iff`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

namespace CategoryTheory

/-- **Points of a relation given by a morphism into a fibre product**: for `j : R ⟶ X ×_S X`, the
points `x, y : T ⟶ X` are related by the two projections of `j` if and only if `(x, y)` factors
through `j`. -/
theorem pointsRelation_comp_fst_comp_snd_iff {C : Type*} [Category C] {R X S : C} {π : X ⟶ S}
    [HasPullback π π] (j : R ⟶ pullback π π) {T : C} (x y : T ⟶ X) (hxy : x ≫ π = y ≫ π) :
    pointsRelation (j ≫ pullback.fst π π) (j ≫ pullback.snd π π) T x y ↔
      ∃ r : T ⟶ R, r ≫ j = pullback.lift x y hxy := by
  constructor
  · rintro ⟨r, h₁, h₂⟩
    exact ⟨r, pullback.hom_ext (by simpa using h₁) (by simpa using h₂)⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, by rw [← Category.assoc, hr, pullback.lift_fst],
      by rw [← Category.assoc, hr, pullback.lift_snd]⟩

end CategoryTheory

namespace AlgebraicGeometry

variable {S Z R : Scheme.{u}} (πZ : Z ⟶ S) (j : R ⟶ pullback πZ πZ)

/-- **A Hilbert datum for the quotient of `Z` by `R`** (what the proof of Nitsure,
arXiv:math/0504590v1, Theorem 6.8, pp. 33–35, uses of the Hilbert scheme): a scheme `H` over `S`,
a closed subscheme `D` of `Z ×_S H` that is flat, proper and surjective over `H`, and a morphism
`φ : Z ⟶ H` over `S` with `φ^* D = R`, that is, `D.comap (𝟙 × φ) = ker j`, such that `T`-points of
`H` over `S` with the same pulled-back family on `Z ×_S T` are equal for `T` locally Noetherian. -/
structure QuotientHilbertDatum where
  /-- The parameter scheme, in Nitsure's proof a finite union of Hilbert schemes of `Z`. -/
  H : Scheme.{u}
  /-- The structure morphism of `H`. -/
  πH : H ⟶ S
  /-- The family over `H`: a closed subscheme of `Z ×_S H`, with `Z` the first factor. -/
  D : (pullback πZ πH).IdealSheafData
  /-- The family is flat over `H`. -/
  flat : Flat (D.subschemeι ≫ pullback.snd πZ πH)
  /-- The family is proper over `H`. -/
  isProper : IsProper (D.subschemeι ≫ pullback.snd πZ πH)
  /-- The family is surjective over `H`: no fibre is empty. -/
  surjective : Surjective (D.subschemeι ≫ pullback.snd πZ πH)
  /-- The classifying morphism of `R`, regarded as a family over `Z` through `pr₂`. -/
  φ : Z ⟶ H
  /-- `φ` is a morphism over `S`. -/
  w : φ ≫ πH = πZ
  /-- `φ^* D = R`: the pullback of `D` along `𝟙 × φ : Z ×_S Z ⟶ Z ×_S H` is `R`. -/
  comap_eq : D.comap (pullback.map πZ πZ πZ πH (𝟙 Z) φ (𝟙 S) (by simp) (by simp [w])) = j.ker
  /-- Points of `H` over `S` are determined by their families, on locally Noetherian `T`. -/
  injective : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (g : T ⟶ S) (a b : T ⟶ H)
    (ha : a ≫ πH = g) (hb : b ≫ πH = g),
    D.comap (pullback.map πZ g πZ πH (𝟙 Z) a (𝟙 S) (by simp) (by simp [ha])) =
      D.comap (pullback.map πZ g πZ πH (𝟙 Z) b (𝟙 S) (by simp) (by simp [hb])) → a = b

namespace QuotientHilbertDatum

variable {πZ j} (𝔥 : QuotientHilbertDatum πZ j)

/-- The projection `p : D ⟶ H` of the family (Nitsure, p. 33). -/
abbrev familyProj : 𝔥.D.subscheme ⟶ 𝔥.H :=
  𝔥.D.subschemeι ≫ pullback.snd πZ 𝔥.πH

instance flat_familyProj : Flat 𝔥.familyProj :=
  𝔥.flat

instance isProper_familyProj : IsProper 𝔥.familyProj :=
  𝔥.isProper

instance surjective_familyProj : Surjective 𝔥.familyProj :=
  𝔥.surjective

/-- **Membership** (Nitsure, arXiv:math/0504590v1, p. 33): for `x : T ⟶ Z` and `V : T ⟶ H` over
`g : T ⟶ S`, the graph `(x, 𝟙_T) : T ⟶ Z ×_S T` factors through the pulled-back family
`D.comap (𝟙 × V)` (Nitsure's `x ∈ V`) if and only if `(x, V) : T ⟶ Z ×_S H` factors through `D`. -/
theorem exists_lift_comap_iff_exists_lift {T : Scheme.{u}} (g : T ⟶ S) (x : T ⟶ Z)
    (V : T ⟶ 𝔥.H) (hx : x ≫ πZ = 𝟙 T ≫ g) (e₁ : πZ ≫ 𝟙 S = 𝟙 Z ≫ πZ)
    (e₂ : g ≫ 𝟙 S = V ≫ 𝔥.πH) (h : x ≫ πZ = V ≫ 𝔥.πH) :
    (∃ a : T ⟶ (𝔥.D.comap (pullback.map πZ g πZ 𝔥.πH (𝟙 Z) V (𝟙 S) e₁ e₂)).subscheme,
        a ≫ (𝔥.D.comap (pullback.map πZ g πZ 𝔥.πH (𝟙 Z) V (𝟙 S) e₁ e₂)).subschemeι =
          pullback.lift x (𝟙 T) hx) ↔
      ∃ d : T ⟶ 𝔥.D.subscheme, d ≫ 𝔥.D.subschemeι = pullback.lift x V h := by
  have key : pullback.lift x (𝟙 T) hx ≫ pullback.map πZ g πZ 𝔥.πH (𝟙 Z) V (𝟙 S) e₁ e₂ =
      pullback.lift x V h := by
    apply pullback.hom_ext <;> simp [pullback.map]
  rw [Scheme.IdealSheafData.exists_lift_comap_subschemeι_iff, key]

/-- `(x, y) ≫ (𝟙 × φ) = (x, φ ∘ y)` as morphisms `T ⟶ Z ×_S H`. -/
theorem lift_comp_map_eq_lift {T : Scheme.{u}} (x y : T ⟶ Z) (hxy : x ≫ πZ = y ≫ πZ)
    (e₁ : πZ ≫ 𝟙 S = 𝟙 Z ≫ πZ) (e₂ : πZ ≫ 𝟙 S = 𝔥.φ ≫ 𝔥.πH)
    (h : x ≫ πZ = (y ≫ 𝔥.φ) ≫ 𝔥.πH) :
    pullback.lift x y hxy ≫ pullback.map πZ πZ πZ 𝔥.πH (𝟙 Z) 𝔥.φ (𝟙 S) e₁ e₂ =
      pullback.lift x (y ≫ 𝔥.φ) h := by
  apply pullback.hom_ext <;> simp [pullback.map]

/-- **The first equivalence of `(***)`** (Nitsure, arXiv:math/0504590v1, p. 34): for a closed
immersion `j` and `x, y : T ⟶ Z`, `(x, y) ∈ R(T)` if and only if `x ∈ φ(y)`, that is, the point
`(x, φ ∘ y)` of `Z ×_S H` factors through `D`. This holds for every scheme `T`. -/
theorem exists_lift_subschemeι_iff_pointsRelation [IsClosedImmersion j] {T : Scheme.{u}}
    (x y : T ⟶ Z) (h : x ≫ πZ = (y ≫ 𝔥.φ) ≫ 𝔥.πH) :
    (∃ d : T ⟶ 𝔥.D.subscheme, d ≫ 𝔥.D.subschemeι = pullback.lift x (y ≫ 𝔥.φ) h) ↔
      pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T x y := by
  have hxy : x ≫ πZ = y ≫ πZ := by rw [h, Category.assoc, 𝔥.w]
  rw [← 𝔥.lift_comp_map_eq_lift x y hxy (by simp) (by simp [𝔥.w]) h,
    ← Scheme.IdealSheafData.exists_lift_comap_subschemeι_iff, 𝔥.comap_eq,
    Scheme.IdealSheafData.exists_lift_subschemeι_iff_le_ker,
    ← Scheme.Hom.exists_lift_iff_ker_le_ker, pointsRelation_comp_fst_comp_snd_iff j x y hxy]

/-- **The first equivalence of `(***)` in Nitsure's form** (arXiv:math/0504590v1, p. 34): for
`x, y : T ⟶ Z` over `g : T ⟶ S`, `(x, y) ∈ R(T)` if and only if `x ∈ φ(y)`, that is,
`(x, 𝟙_T) : T ⟶ Z ×_S T` factors through the family `φ(y) = (y ≫ φ)^* D`. -/
theorem pointsRelation_iff_exists_lift_comap [IsClosedImmersion j] {T : Scheme.{u}} (g : T ⟶ S)
    (x y : T ⟶ Z) (hx : x ≫ πZ = 𝟙 T ≫ g) (e₁ : πZ ≫ 𝟙 S = 𝟙 Z ≫ πZ)
    (e₂ : g ≫ 𝟙 S = (y ≫ 𝔥.φ) ≫ 𝔥.πH) :
    pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T x y ↔
      ∃ a : T ⟶ (𝔥.D.comap (pullback.map πZ g πZ 𝔥.πH (𝟙 Z) (y ≫ 𝔥.φ) (𝟙 S) e₁ e₂)).subscheme,
        a ≫ (𝔥.D.comap (pullback.map πZ g πZ 𝔥.πH (𝟙 Z) (y ≫ 𝔥.φ) (𝟙 S) e₁ e₂)).subschemeι =
          pullback.lift x (𝟙 T) hx := by
  have h : x ≫ πZ = (y ≫ 𝔥.φ) ≫ 𝔥.πH := by rw [hx, Category.id_comp, ← e₂, Category.comp_id]
  rw [𝔥.exists_lift_comap_iff_exists_lift g x (y ≫ 𝔥.φ) hx e₁ e₂ h,
    𝔥.exists_lift_subschemeι_iff_pointsRelation x y h]

/-- **`y^* R = φ(y)`** (Nitsure, arXiv:math/0504590v1, p. 34): for `y : T ⟶ Z` over
`g : T ⟶ S`, the pullback of `R` along `𝟙 × y : Z ×_S T ⟶ Z ×_S Z` is the family
`φ(y) = (y ≫ φ)^* D` on `Z ×_S T`. -/
theorem ker_comap_eq_comap {T : Scheme.{u}} (g : T ⟶ S) (y : T ⟶ Z) (e₁ : πZ ≫ 𝟙 S = 𝟙 Z ≫ πZ)
    (e₂ : g ≫ 𝟙 S = y ≫ πZ) (e₂' : g ≫ 𝟙 S = (y ≫ 𝔥.φ) ≫ 𝔥.πH) :
    j.ker.comap (pullback.map πZ g πZ πZ (𝟙 Z) y (𝟙 S) e₁ e₂) =
      𝔥.D.comap (pullback.map πZ g πZ 𝔥.πH (𝟙 Z) (y ≫ 𝔥.φ) (𝟙 S) e₁ e₂') := by
  rw [← 𝔥.comap_eq, ← Scheme.IdealSheafData.comap_comp]
  congr 1
  apply pullback.hom_ext <;> simp [pullback.map]

/-- **Points of `D` over `φ ∘ y`**: if a `T`-point `d` of `D` lies over `φ ∘ y` in `H`, its first
coordinate `x` is `R`-related to `y`, since `d = (x, φ ∘ y)` (the first equivalence of `(***)`). -/
theorem pointsRelation_of_comp_familyProj_eq [IsClosedImmersion j] {T : Scheme.{u}}
    (d : T ⟶ 𝔥.D.subscheme) (y : T ⟶ Z) (h : d ≫ 𝔥.familyProj = y ≫ 𝔥.φ) :
    pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T
      (d ≫ 𝔥.D.subschemeι ≫ pullback.fst πZ 𝔥.πH) y := by
  have hx : (d ≫ 𝔥.D.subschemeι ≫ pullback.fst πZ 𝔥.πH) ≫ πZ = (y ≫ 𝔥.φ) ≫ 𝔥.πH := by
    rw [← h]
    simp [familyProj, pullback.condition]
  refine (𝔥.exists_lift_subschemeι_iff_pointsRelation _ y hx).mp ⟨d, ?_⟩
  apply pullback.hom_ext
  · simp
  · simpa [familyProj] using h

end QuotientHilbertDatum

end AlgebraicGeometry
