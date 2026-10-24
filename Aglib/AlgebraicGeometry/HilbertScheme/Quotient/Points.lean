/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Datum

/-!
# Nitsure's `(***)` on locally Noetherian points

Let `𝔥 = (H, D, φ)` be a Hilbert datum (`QuotientHilbertDatum`) for `πZ : Z ⟶ S` and a closed
immersion `j : R ⟶ Z ×_S Z` with projections `p₁ = j ≫ pr₁`, `p₂ = j ≫ pr₂`, and suppose that the
relation `pointsRelation p₁ p₂ T` on `T`-points of `Z` is an equivalence relation for every locally
Noetherian `T` (Nitsure's schematic equivalence relation, tested on locally Noetherian points; see
`Aglib.AlgebraicGeometry.Properties.Noetherian.EquivalenceRelation`). Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, proof of Theorem 6.8, p. 34:

> `(***)` For any `S`-scheme `T`, and `T`-valued points `x, y ∈ X(T)`, the following equivalences
> hold: `(x, y) ∈ R(T) ⇔ x ∈ φ(y) ⇔ φ(x) = φ(y) ∈ H(T)`.

* `QuotientHilbertDatum.pointsRelation_iff_comp_eq`: for `T` locally Noetherian and `πZ` locally of
  finite type, `(x, y) ∈ R(T)` if and only if `x ≫ φ = y ≫ φ`. The first equivalence of `(***)` is
  `QuotientHilbertDatum.exists_lift_subschemeι_iff_pointsRelation` (all `T`).

The proof follows Nitsure. If `x ≫ φ = y ≫ φ`, then `x ∈ φ(x) = φ(y)` by reflexivity. Conversely,
if `(x, y) ∈ R(T)`, the families `x^* R = (x ≫ φ)^* D` and `y^* R = (y ≫ φ)^* D` on `Z ×_S T` have
the same `U`-points `(z, u)`: `(z, u ≫ x) ∈ R(U)` if and only if `(z, u ≫ y) ∈ R(U)`, by symmetry
and transitivity at `U`. Here the test schemes `U` are locally Noetherian, and `Z ×_S T` is locally
Noetherian (locally of finite type over `T`), so the two closed subschemes are equal
(`Scheme.IdealSheafData.comap_eq_comap_of_locallyNoetherian_exists_lift_iff`); the injectivity
field of `𝔥` then gives `x ≫ φ = y ≫ φ`. Nitsure quantifies over all `S`-schemes `T` and `U`; the
restriction to locally Noetherian test schemes is needed because the Hilbert scheme represents its
functor on locally Noetherian schemes only, and it suffices because every scheme tested below is
locally Noetherian.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

namespace AlgebraicGeometry.QuotientHilbertDatum

variable {S Z R : Scheme.{u}} {πZ : Z ⟶ S} {j : R ⟶ pullback πZ πZ}
  (𝔥 : QuotientHilbertDatum πZ j)

/-- `w ≫ (𝟙 × (x ≫ φ)) = (w ≫ pr₁, (w ≫ pr₂ ≫ x) ≫ φ)` for a `U`-point `w` of `Z ×_S T`. -/
theorem comp_map_comp_eq_lift {T U : Scheme.{u}} (g : T ⟶ S) (x : T ⟶ Z)
    (e₁ : πZ ≫ 𝟙 S = 𝟙 Z ≫ πZ) (e₂ : g ≫ 𝟙 S = (x ≫ 𝔥.φ) ≫ 𝔥.πH) (w : U ⟶ pullback πZ g)
    (h : (w ≫ pullback.fst πZ g) ≫ πZ = (((w ≫ pullback.snd πZ g) ≫ x) ≫ 𝔥.φ) ≫ 𝔥.πH) :
    w ≫ pullback.map πZ g πZ 𝔥.πH (𝟙 Z) (x ≫ 𝔥.φ) (𝟙 S) e₁ e₂ =
      pullback.lift (w ≫ pullback.fst πZ g) (((w ≫ pullback.snd πZ g) ≫ x) ≫ 𝔥.φ) h := by
  apply pullback.hom_ext <;> simp [pullback.map]

/-- **Nitsure's `(***)` on locally Noetherian points** (arXiv:math/0504590v1, p. 34): for a
closed immersion `j` whose relation on locally Noetherian points is an equivalence relation, `πZ`
locally of finite type, and `T` locally Noetherian, two points `x, y : T ⟶ Z` are `R`-related if
and only if `φ(x) = φ(y)`. -/
theorem pointsRelation_iff_comp_eq [IsClosedImmersion j] [LocallyOfFiniteType πZ]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T))
    {T : Scheme.{u}} [IsLocallyNoetherian T] (x y : T ⟶ Z) :
    pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T x y ↔
      x ≫ 𝔥.φ = y ≫ 𝔥.φ := by
  constructor
  · intro hr
    have hxy : x ≫ πZ = y ≫ πZ := by
      obtain ⟨r, rfl, rfl⟩ := hr
      simp only [Category.assoc, pullback.condition]
    refine 𝔥.injective T (x ≫ πZ) (x ≫ 𝔥.φ) (y ≫ 𝔥.φ) (by rw [Category.assoc, 𝔥.w])
      (by rw [Category.assoc, 𝔥.w, hxy]) ?_
    refine Scheme.IdealSheafData.comap_eq_comap_of_locallyNoetherian_exists_lift_iff _ _ _
      fun U _ w => ?_
    have hU := hr.comp (w ≫ pullback.snd πZ (x ≫ πZ))
    have h₁ : (w ≫ pullback.fst πZ (x ≫ πZ)) ≫ πZ =
        (((w ≫ pullback.snd πZ (x ≫ πZ)) ≫ x) ≫ 𝔥.φ) ≫ 𝔥.πH := by
      simp [𝔥.w, pullback.condition]
    have h₂ : (w ≫ pullback.fst πZ (x ≫ πZ)) ≫ πZ =
        (((w ≫ pullback.snd πZ (x ≫ πZ)) ≫ y) ≫ 𝔥.φ) ≫ 𝔥.πH := by
      have e : (((w ≫ pullback.snd πZ (x ≫ πZ)) ≫ y) ≫ 𝔥.φ) ≫ 𝔥.πH =
          (w ≫ pullback.snd πZ (x ≫ πZ)) ≫ y ≫ πZ := by
        simp [𝔥.w]
      rw [e, ← hxy]
      simp [pullback.condition]
    rw [𝔥.comp_map_comp_eq_lift _ x _ _ w h₁, 𝔥.comp_map_comp_eq_lift _ y _ _ w h₂,
      𝔥.exists_lift_subschemeι_iff_pointsRelation, 𝔥.exists_lift_subschemeι_iff_pointsRelation]
    exact ⟨fun h => (hequiv U).trans h hU, fun h => (hequiv U).trans h ((hequiv U).symm hU)⟩
  · intro hφ
    have h : x ≫ πZ = (y ≫ 𝔥.φ) ≫ 𝔥.πH := by rw [← hφ, Category.assoc, 𝔥.w]
    have h' : x ≫ πZ = (x ≫ 𝔥.φ) ≫ 𝔥.πH := by rw [Category.assoc, 𝔥.w]
    obtain ⟨d, hd⟩ :=
      (𝔥.exists_lift_subschemeι_iff_pointsRelation x x h').mpr ((hequiv T).refl x)
    refine (𝔥.exists_lift_subschemeι_iff_pointsRelation x y h).mp ⟨d, hd.trans ?_⟩
    exact pullback.hom_ext (by simp) (by simp [hφ])

end AlgebraicGeometry.QuotientHilbertDatum
