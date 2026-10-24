/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Descent
public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.FlatProper

/-!
# The quotient is effective

Let `𝔥 = (H, D, φ)` be a Hilbert datum (`QuotientHilbertDatum`) for `πZ : Z ⟶ S` and a closed
immersion `j : R ⟶ Z ×_S Z` with projections `p₁ = j ≫ pr₁`, `p₂ = j ≫ pr₂`, whose relation on
locally Noetherian points is an equivalence relation, with `Z` locally Noetherian, `πZ` locally of
finite type and `H` separated over `S` and locally Noetherian. Let `q = φ.toImage : Z ⟶ Q = φ.image`
be the quotient morphism of `Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Descent`. Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, proof of Theorem 6.8, p. 35,
(iii): by `(***)`, `(x, y) ∈ R(T)` if and only if `φ(x) = φ(y)`, so `p₁ ≫ q = p₂ ≫ q` and
`(p₁, p₂) : R ⟶ Z ×_Q Z` is an isomorphism, "by showing these statements hold at the level of
functor of points".

* `QuotientHilbertDatum.comp_toImage_eq`: `p₁ ≫ q = p₂ ≫ q`, from `(***)` at the identity point
  of `R` (`R` is locally Noetherian) and the monomorphism `ι_Q`.
* `QuotientHilbertDatum.isIso_lift_toImage`: `(p₁, p₂) : R ⟶ Z ×_Q Z` is an isomorphism. It is
  bijective on `T`-points for `T` locally Noetherian (injective as `j` is a monomorphism,
  surjective by `(***)`), and `R` and `Z ×_Q Z` are locally Noetherian, so the locally Noetherian
  Yoneda lemma applies (`Scheme.isIso_of_locallyNoetherian_yoneda_map_bijective`).
* `QuotientHilbertDatum.isPullback_toImage`: the square `(p₁, p₂, q, q)` is cartesian.
* `QuotientHilbertDatum.flatProperQuotient`: over `S = Spec A`, if `H` is H-quasi-projective over
  `Spec A`, then `(Q, ι_Q ≫ πH, q)` is a `FlatProperQuotient πZ p₁ p₂`; `Q` is H-quasi-projective
  as a closed subscheme of `H` (Nitsure, p. 35, (i)).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

namespace AlgebraicGeometry.QuotientHilbertDatum

section Effective

variable {S Z R : Scheme.{u}} {πZ : Z ⟶ S} {j : R ⟶ pullback πZ πZ}
  (𝔥 : QuotientHilbertDatum πZ j)

/-- **The quotient morphism coequalizes the relation** (Nitsure, arXiv:math/0504590v1, p. 35,
(iii)): `p₁ ≫ q = p₂ ≫ q`, by `(***)` at the identity point of `R`. -/
theorem comp_toImage_eq [IsClosedImmersion j] [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    (j ≫ pullback.fst πZ πZ) ≫ 𝔥.φ.toImage = (j ≫ pullback.snd πZ πZ) ≫ 𝔥.φ.toImage := by
  have : IsLocallyNoetherian R := LocallyOfFiniteType.isLocallyNoetherian j
  rw [← cancel_mono 𝔥.φ.imageι]
  simpa using (𝔥.pointsRelation_iff_comp_eq hequiv (j ≫ pullback.fst πZ πZ)
    (j ≫ pullback.snd πZ πZ)).mp ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩

/-- **The quotient is effective** (Nitsure, arXiv:math/0504590v1, p. 35, (iii)): the morphism
`(p₁, p₂) : R ⟶ Z ×_Q Z` is an isomorphism. -/
theorem isIso_lift_toImage [IsClosedImmersion j] [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ]
    [IsSeparated 𝔥.πH] [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    IsIso (pullback.lift (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ)
      (𝔥.comp_toImage_eq hequiv)) := by
  have : IsLocallyNoetherian R := LocallyOfFiniteType.isLocallyNoetherian j
  have := 𝔥.isProper_toImage hequiv
  refine Scheme.isIso_of_locallyNoetherian_yoneda_map_bijective _ fun T _ => ⟨?_, ?_⟩
  · intro r r' h
    have h₁ := congrArg (· ≫ pullback.fst 𝔥.φ.toImage 𝔥.φ.toImage) h
    have h₂ := congrArg (· ≫ pullback.snd 𝔥.φ.toImage 𝔥.φ.toImage) h
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at h₁ h₂
    exact (cancel_mono j).mp (pullback.hom_ext (by simpa using h₁) (by simpa using h₂))
  · intro t
    have e : pullback.fst 𝔥.φ.toImage 𝔥.φ.toImage ≫ 𝔥.φ =
        pullback.snd 𝔥.φ.toImage 𝔥.φ.toImage ≫ 𝔥.φ := by
      have e' := congrArg (· ≫ 𝔥.φ.imageι)
        (pullback.condition (f := 𝔥.φ.toImage) (g := 𝔥.φ.toImage))
      simpa using e'
    have hq : (t ≫ pullback.fst 𝔥.φ.toImage 𝔥.φ.toImage) ≫ 𝔥.φ =
        (t ≫ pullback.snd 𝔥.φ.toImage 𝔥.φ.toImage) ≫ 𝔥.φ := by
      simp only [Category.assoc, e]
    obtain ⟨r, hr₁, hr₂⟩ := (𝔥.pointsRelation_iff_comp_eq hequiv _ _).mpr hq
    exact ⟨r, pullback.hom_ext (by simpa using hr₁) (by simpa using hr₂)⟩

/-- **The relation is the kernel pair of the quotient morphism** (Nitsure, arXiv:math/0504590v1,
p. 35, (iii)): the square `(p₁, p₂, q, q)` is cartesian. -/
theorem isPullback_toImage [IsClosedImmersion j] [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ]
    [IsSeparated 𝔥.πH] [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    IsPullback (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) 𝔥.φ.toImage 𝔥.φ.toImage := by
  have := 𝔥.isIso_lift_toImage hequiv
  exact IsPullback.of_iso_pullback ⟨𝔥.comp_toImage_eq hequiv⟩
    (asIso (pullback.lift _ _ (𝔥.comp_toImage_eq hequiv))) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

end Effective

section AffineBase

variable {A : Type u} [CommRing A] {Z R : Scheme.{u}} {πZ : Z ⟶ Spec (.of A)}
  {j : R ⟶ pullback πZ πZ}

/-- **The quotient by a flat proper equivalence relation** (Nitsure, arXiv:math/0504590v1,
Theorem 6.8, pp. 33–35, over `S = Spec A`, from a Hilbert datum, on locally Noetherian points):
let `j : R ⟶ Z ×_{Spec A} Z` be a closed immersion whose relation on locally Noetherian points is an
equivalence relation, with `Z` locally Noetherian and locally of finite type over `Spec A`, and let
`𝔥` be a Hilbert datum with `H` H-quasi-projective and locally Noetherian. Then the
scheme-theoretic image `Q` of `φ`, with `q = φ.toImage`, is a flat proper quotient of `Z` by
`(j ≫ pr₁, j ≫ pr₂)`. -/
def flatProperQuotient (𝔥 : QuotientHilbertDatum πZ j) [IsClosedImmersion j]
    [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ] [IsHQuasiProjective 𝔥.πH]
    [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    FlatProperQuotient πZ (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) where
  Q := 𝔥.φ.image
  πQ := 𝔥.φ.imageι ≫ 𝔥.πH
  q := 𝔥.φ.toImage
  fac := by rw [Scheme.Hom.toImage_imageι_assoc, 𝔥.w]
  isHQuasiProjective := inferInstance
  flat := 𝔥.flat_toImage hequiv
  surjective := 𝔥.surjective_toImage hequiv
  isProper := 𝔥.isProper_toImage hequiv
  isPullback := 𝔥.isPullback_toImage hequiv

@[simp]
theorem flatProperQuotient_q (𝔥 : QuotientHilbertDatum πZ j) [IsClosedImmersion j]
    [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ] [IsHQuasiProjective 𝔥.πH]
    [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    (𝔥.flatProperQuotient hequiv).q = 𝔥.φ.toImage :=
  rfl

/-- The quotient morphism followed by the closed immersion `Q ⟶ H` is the classifying morphism
(Nitsure, arXiv:math/0504590v1, p. 35: "the composite `X → Q ↪ H` equals `φ`"). -/
theorem flatProperQuotient_q_imageι (𝔥 : QuotientHilbertDatum πZ j) [IsClosedImmersion j]
    [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ] [IsHQuasiProjective 𝔥.πH]
    [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    (𝔥.flatProperQuotient hequiv).q ≫ 𝔥.φ.imageι = 𝔥.φ :=
  Scheme.Hom.toImage_imageι 𝔥.φ

/-- **Existence of the quotient from a Hilbert datum**, for a relation given by `p₁, p₂ : R ⟶ Z`
with `j ≫ pr₁ = p₁` and `j ≫ pr₂ = p₂` (the form in which the core is applied to a schematic
equivalence relation, `j = (p₁, p₂)`; Nitsure, arXiv:math/0504590v1, Theorem 6.8, pp. 33–35). -/
theorem nonempty_flatProperQuotient_of_comp_eq (𝔥 : QuotientHilbertDatum πZ j) {p₁ p₂ : R ⟶ Z}
    (hj₁ : j ≫ pullback.fst πZ πZ = p₁) (hj₂ : j ≫ pullback.snd πZ πZ = p₂) [IsClosedImmersion j]
    [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ] [IsHQuasiProjective 𝔥.πH]
    [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation p₁ p₂ T)) :
    Nonempty (FlatProperQuotient πZ p₁ p₂) := by
  subst hj₁ hj₂
  exact ⟨𝔥.flatProperQuotient hequiv⟩

end AffineBase

end AlgebraicGeometry.QuotientHilbertDatum
