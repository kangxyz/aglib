/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Point
public import Aglib.AlgebraicGeometry.IdealSheaf.QuotientModule
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Basic

/-!
# The Hilbert functor of projective space

Let `A` be a ring, `ι` a coordinate type and `Φ : ℚ[X]`. For a scheme `T` with `g : T ⟶ Spec A`,
the Hilbert functor (Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1,
§1, pp. 3–4) assigns to `T` the closed subschemes `Z ⊆ P^n_A ×_{Spec A} T` that are flat over `T`
and whose fibers have Hilbert polynomial `Φ`. Closed subschemes are Mathlib's
`Scheme.IdealSheafData`, flatness over `T` is Mathlib's `Flat` for `Z ⟶ P^n_A ×_{Spec A} T ⟶ T`,
and the functor acts by `IdealSheafData.comap` along the base-changed map
`baseChangeMap ι g g' f h : P^n_A ×_{Spec A} T' ⟶ P^n_A ×_{Spec A} T`
(`ProjectiveSpace/BaseChange/Point`). The fiber of `Z` at a field point `x : Spec K ⟶ T` is
`Z.comap (pointMap ι g x)`, a closed subscheme of `P^n_K`; its structure module is
`quotientModule` (`IdealSheaf/QuotientModule`).

* `ProjectiveSpace.subschemeHilbertPolynomial ι k W`, the Hilbert polynomial of `𝒪_W` for
  `W ⊆ P^n_k` over a field `k`.
* `ProjectiveSpace.IsHilbertFamily ι Φ g Z`: `Z` is flat over `T` and its fiber at every field
  point `x : Spec K ⟶ T` has Hilbert polynomial `Φ`.
* `ProjectiveSpace.hilbertFunctor ι Φ : (Over (Spec A))ᵒᵖ ⥤ Type u`, defined on all schemes over
  `Spec A`; Nitsure's statements restrict it to locally Noetherian test schemes.
* `ProjectiveSpace.IsHilbertFamily.comap`: pullback along a morphism over `Spec A` preserves
  flatness (base change of a flat morphism) and the fiber Hilbert polynomials (the fiber of the
  pullback at `x` is the fiber at the image point, `pointMap_comp_baseChangeMap`).

The fiber condition quantifies over all field points rather than over the residue fields
`κ(t)` of the points `t ∈ T`. Every field point factors through some `Spec κ(t)`, and Hilbert
polynomials are invariant under field extension, so the two conditions agree; this is
`isHilbertFamily_iff_residueField` (`HilbertScheme/ResidueField`). The field-point form makes the
fibers of an affine test scheme `Spec B` at the residue fields `κ(p)` of its primes direct
instances.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

variable (ι : Type u)

/-- The Hilbert polynomial of a closed subscheme `W` of `P^n_k` over a field `k`: the Hilbert
polynomial of its structure module `𝒪_W = 𝒪 / I_W`. -/
def subschemeHilbertPolynomial (k : Type u) [Field k]
    (W : (ProjectiveSpace k ι).IdealSheafData) : ℚ[X] :=
  Scheme.Cohomology.projectiveHilbertPolynomial k ι W.quotientModule

variable {A : Type u} [CommRing A]

/-- **Points of the Hilbert functor** (Nitsure, arXiv:math/0504590v1, §1, pp. 3–4): a closed
subscheme `Z ⊆ P^n_A ×_{Spec A} T` that is flat over `T` and whose fiber at every field point
`x : Spec K ⟶ T` has Hilbert polynomial `Φ`. -/
structure IsHilbertFamily (Φ : ℚ[X]) {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (Z : (pullback (toSpec A ι) g).IdealSheafData) : Prop where
  /-- `Z` is flat over `T`. -/
  flat : Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g)
  /-- Every fiber of `Z` over a field point of `T` has Hilbert polynomial `Φ`. -/
  subschemeHilbertPolynomial_fiber (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T) :
    subschemeHilbertPolynomial ι K (Z.comap (pointMap ι g x)) = Φ

/-- **Pullback preserves flat families with Hilbert polynomial `Φ`**: for `f : T' ⟶ T` over
`Spec A`, the pullback of `Z` along the base-changed map is flat over `T'` (base change of a flat
morphism) and its fiber at `x` is the fiber of `Z` at `x ≫ f`. -/
theorem IsHilbertFamily.comap {Φ : ℚ[X]} {T T' : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
    {g' : T' ⟶ Spec (CommRingCat.of A)} (f : T' ⟶ T) (h : f ≫ g = g')
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z) :
    IsHilbertFamily ι Φ g' (Z.comap (baseChangeMap ι g g' f h)) where
  flat := by
    have := hZ.flat
    let b := baseChangeMap ι g g' f h
    have hsq : IsPullback (pullback.snd b Z.subschemeι)
        (pullback.fst b Z.subschemeι ≫ pullback.snd (toSpec A ι) g')
        (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) f :=
      (IsPullback.of_hasPullback b Z.subschemeι).flip.paste_vert
        (isPullback_baseChangeMap ι g g' f h)
    have hfl : Flat (pullback.fst b Z.subschemeι ≫ pullback.snd (toSpec A ι) g') :=
      MorphismProperty.of_isPullback hsq this
    rw [← Scheme.IdealSheafData.comapIso_hom_fst Z b, Category.assoc]
    infer_instance
  subschemeHilbertPolynomial_fiber K _ x := by
    rw [← Scheme.IdealSheafData.comap_comp, pointMap_comp_baseChangeMap]
    exact hZ.subschemeHilbertPolynomial_fiber K (x ≫ f)

/-- **The Hilbert functor** `Hilb^Φ` of `P^n_A` (Nitsure, arXiv:math/0504590v1, §1, pp. 3–4), on all
schemes `T` over `Spec A`: `T` goes to the closed subschemes of `P^n_A ×_{Spec A} T` that are flat
over `T` with all fiber Hilbert polynomials `Φ`, and `f : T' ⟶ T` acts by pullback along the
base-changed map. Nitsure's representability statements concern locally Noetherian `T`. -/
def hilbertFunctor (Φ : ℚ[X]) : (Over (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u where
  obj T := {Z : (pullback (toSpec A ι) T.unop.hom).IdealSheafData //
    IsHilbertFamily ι Φ T.unop.hom Z}
  map {T T'} f := TypeCat.ofHom fun Z =>
    ⟨Z.1.comap (baseChangeMap ι T.unop.hom T'.unop.hom f.unop.left (Over.w f.unop)),
      Z.2.comap ι f.unop.left (Over.w f.unop)⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun Z => Subtype.ext ?_
    change Z.1.comap (baseChangeMap ι _ _ (𝟙 T.unop.left) _) = Z.1
    rw [baseChangeMap_id, Scheme.IdealSheafData.comap_id]
  map_comp {T T' T''} f f' := by
    refine ConcreteCategory.hom_ext _ _ fun Z => Subtype.ext ?_
    change Z.1.comap (baseChangeMap ι _ _ (f'.unop.left ≫ f.unop.left) _) =
      (Z.1.comap (baseChangeMap ι _ _ f.unop.left _)).comap (baseChangeMap ι _ _ f'.unop.left _)
    rw [baseChangeMap_comp ι _ _ _ _ _ (Over.w f.unop) (Over.w f'.unop),
      Scheme.IdealSheafData.comap_comp]

theorem hilbertFunctor_map_coe (Φ : ℚ[X]) {T T' : (Over (Spec (CommRingCat.of A)))ᵒᵖ}
    (f : T ⟶ T') (Z : (hilbertFunctor ι Φ).obj T) :
    Subtype.val ((hilbertFunctor ι Φ).map f Z) =
      Z.1.comap (baseChangeMap ι T.unop.hom T'.unop.hom f.unop.left (Over.w f.unop)) :=
  rfl

end ProjectiveSpace

end AlgebraicGeometry
