/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.IdealSheaf.FaithfullyFlat
public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Graph

/-!
# The quotient as the scheme-theoretic image of the classifying morphism

Let `𝔥 = (H, D, φ)` be a Hilbert datum (`QuotientHilbertDatum`) for `πZ : Z ⟶ S` and a closed
immersion `j : R ⟶ Z ×_S Z` whose relation on locally Noetherian points is an equivalence relation,
with `Z` locally Noetherian, `πZ` locally of finite type and `H` separated over `S` and locally
Noetherian. Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, proof of
Theorem 6.8, p. 35: Lemma 6.7(2), applied to the faithfully flat quasi-compact `p : D ⟶ H` and the
closed subscheme `Γ_φ ⊂ D` with `p₁⁻¹ Γ_φ = p₂⁻¹ Γ_φ`, gives a unique closed subscheme `Q ⊂ H`
with `Γ_φ = p⁻¹ Q`; the quotient morphism `q : X ⟶ Q` is `X ≅ Γ_φ ⟶ Q`, and `X ⟶ Q ↪ H` is `φ`.
By (ii), `q` is faithfully flat and projective by base change from the faithfully flat projective
`p`, as the square `(Γ_φ, q, p, Q ↪ H)` is cartesian; here `p` is flat, surjective and proper, and
so is `q`.

Here `Q` is the scheme-theoretic image `φ.image` of `φ` (Mathlib's `Scheme.Hom.image`, the closed
subscheme of `H` with ideal `ker φ`), `q = φ.toImage` and `Q ↪ H` is `φ.imageι`, so that
`q ≫ ι_Q = φ` (`Scheme.Hom.toImage_imageι`). Lemma 6.7(2) is
`Scheme.IdealSheafData.comap_map_eq_self_of_flat_of_surjective`
(`Aglib.AlgebraicGeometry.Descent.IdealSheaf.FaithfullyFlat`): the descended ideal of `Γ_φ` is
`(ker Γ).map p = ker (Γ ≫ p) = ker φ`, and any closed subscheme of `H` with base change `Γ_φ` has
this ideal (`ker_eq_ker_comp_of_isPullback_of_flat_of_surjective`).

* `QuotientHilbertDatum.isPullback_toImage_of_comp_subschemeι_eq_graph`: for `Γ` with
  `Γ ≫ D.subschemeι = graph`, the square `Γ, q, p, ι_Q` is cartesian.
* `QuotientHilbertDatum.exists_isPullback_toImage`: such a `Γ` exists.
* `QuotientHilbertDatum.flat_toImage`, `surjective_toImage`, `isProper_toImage`: `q` is flat,
  surjective and proper (base change of `p`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.QuotientHilbertDatum

variable {S Z R : Scheme.{u}} {πZ : Z ⟶ S} {j : R ⟶ pullback πZ πZ}
  (𝔥 : QuotientHilbertDatum πZ j)

/-- **Lemma 6.7(2) for `Γ_φ ⊂ D`** (Nitsure, arXiv:math/0504590v1, p. 35): for `Γ` with
`Γ ≫ D.subschemeι = graph`, the square formed by `Γ : Z ⟶ D`, `q = φ.toImage : Z ⟶ Q`,
`p : D ⟶ H` and `ι_Q = φ.imageι : Q ⟶ H` is cartesian. -/
theorem isPullback_toImage_of_comp_subschemeι_eq_graph [IsClosedImmersion j]
    [LocallyOfFiniteType πZ] [IsSeparated 𝔥.πH] [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T))
    {Γ : Z ⟶ 𝔥.D.subscheme} (hΓ : Γ ≫ 𝔥.D.subschemeι = 𝔥.graph) :
    IsPullback Γ 𝔥.φ.toImage 𝔥.familyProj 𝔥.φ.imageι := by
  have := isClosedImmersion_of_comp_subschemeι_eq_graph hΓ
  refine isPullback_of_isClosedImmersion Γ 𝔥.φ.imageι 𝔥.φ.toImage 𝔥.familyProj ?_ ?_
  · rw [Scheme.Hom.toImage_imageι, comp_familyProj_of_comp_subschemeι_eq_graph hΓ]
  · rw [Scheme.IdealSheafData.ker_subschemeι, ← comp_familyProj_of_comp_subschemeι_eq_graph hΓ,
      Scheme.Hom.ker_comp]
    exact Scheme.IdealSheafData.comap_map_eq_self_of_flat_of_surjective _ _
      (ker_comap_fst_eq_ker_comap_snd_of_comp_subschemeι_eq_graph hΓ hequiv)

/-- **The descent square** (Nitsure, arXiv:math/0504590v1, p. 35, (ii)): the graph factors through
`D` as `Γ : Z ⟶ D`, and the square `Γ, q = φ.toImage, p, ι_Q = φ.imageι` is cartesian. -/
theorem exists_isPullback_toImage [IsClosedImmersion j] [IsLocallyNoetherian Z]
    [LocallyOfFiniteType πZ] [IsSeparated 𝔥.πH] [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    ∃ Γ : Z ⟶ 𝔥.D.subscheme, Γ ≫ 𝔥.D.subschemeι = 𝔥.graph ∧
      IsPullback Γ 𝔥.φ.toImage 𝔥.familyProj 𝔥.φ.imageι := by
  obtain ⟨Γ, hΓ⟩ := 𝔥.exists_comp_subschemeι_eq_graph ((hequiv Z).refl (𝟙 Z))
  exact ⟨Γ, hΓ, 𝔥.isPullback_toImage_of_comp_subschemeι_eq_graph hequiv hΓ⟩

/-- **The quotient morphism is flat**, by base change from `p : D ⟶ H`. -/
theorem flat_toImage [IsClosedImmersion j] [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ]
    [IsSeparated 𝔥.πH] [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    Flat 𝔥.φ.toImage := by
  obtain ⟨Γ, -, H⟩ := 𝔥.exists_isPullback_toImage hequiv
  exact MorphismProperty.of_isPullback (P := @Flat) H inferInstance

/-- **The quotient morphism is surjective**, by base change from `p : D ⟶ H`. -/
theorem surjective_toImage [IsClosedImmersion j] [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ]
    [IsSeparated 𝔥.πH] [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    Surjective 𝔥.φ.toImage := by
  obtain ⟨Γ, -, H⟩ := 𝔥.exists_isPullback_toImage hequiv
  exact MorphismProperty.of_isPullback (P := @Surjective) H inferInstance

/-- **The quotient morphism is proper**, by base change from `p : D ⟶ H`. -/
theorem isProper_toImage [IsClosedImmersion j] [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ]
    [IsSeparated 𝔥.πH] [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    IsProper 𝔥.φ.toImage := by
  obtain ⟨Γ, -, H⟩ := 𝔥.exists_isPullback_toImage hequiv
  exact MorphismProperty.of_isPullback (P := @IsProper) H inferInstance

end AlgebraicGeometry.QuotientHilbertDatum
