/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.FlatteningBridge
public import Aglib.AlgebraicGeometry.IdealSheaf.EmptySubscheme
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.ZeroModule

/-!
# Nonempty closed subschemes of projective space have nonzero Hilbert polynomial

Let `K` be a field and `ι ≃ Fin (n + 1)`. For a closed subscheme `W ⊆ P^n_K`
(`W : (ProjectiveSpace K ι).IdealSheafData`):

* `ProjectiveSpace.subschemeHilbertPolynomial_eq_zero_iff`: the Hilbert polynomial of `W` is zero
  exactly when `W` is empty, `W = ⊤`;
* `ProjectiveSpace.subschemeHilbertPolynomial_ne_zero_iff`: it is nonzero exactly when `W` has a
  point;
* `ProjectiveSpace.subschemeHilbertPolynomial_top`: the empty subscheme has Hilbert polynomial `0`
  (no condition on `ι`).

The proof combines `𝒪_W = 0 ↔ W = ⊤` (`IdealSheafData.isZero_quotientModule_iff`) with the
vanishing criterion for coherent modules `projectiveHilbertPolynomial_eq_zero_iff`
(`Cohomology/Projective/HilbertPolynomial/ZeroModule`: regularity, `h^0(𝒪_W(m)) = Φ(m)` and global
generation of `𝒪_W(m)` for `m ≫ 0`, Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Lemma 2.1 (c), p. 10). Nitsure uses the statement without proof in the proof
of Thm 6.8, p. 33: "If X is non-empty then each fiber of f₂ : R → X is also non-empty as the
diagonal Δ_X is contained in R, and therefore the Hilbert polynomial of each fiber is non-zero.
Hence p : D → H is surjective". Stacks has no direct statement (compare Tag 08AE, and Tags 0BEN
and 0BEV for an indirect route).

**Families.** For a closed subscheme `Z ⊆ P^n_A ×_{Spec A} T` and `t ∈ T`, the fibre
`Z.comap (pointMap ι g (T.fromSpecResidueField t))` is nonempty exactly when `t` lies under a
point of `Z` (`ProjectiveSpace.nonempty_subscheme_comap_fromSpecResidueField_iff`, from the form
`ProjectiveSpace.nonempty_subscheme_comap_pointMap_iff` for an arbitrary point `Spec K ⟶ T`; no
flatness and no Noetherian hypothesis). Hence, for a point `Z` of `Hilb^Φ(T)`:

* `ProjectiveSpace.IsHilbertFamily.surjective_of_ne_zero`: if `Φ ≠ 0`, then `Z ⟶ T` is
  surjective (the surjectivity of `p : D → H` in Nitsure, p. 33);
* `ProjectiveSpace.IsHilbertFamily.ne_zero_of_nonempty`: if `Z` has a point, then `Φ ≠ 0` (every
  polynomial occurring for the fibres of `f₂`, Nitsure, p. 33, is nonzero);
* `ProjectiveSpace.IsHilbertFamily.surjective_iff_ne_zero`: over a nonempty `T`, `Z ⟶ T` is
  surjective exactly when `Φ ≠ 0`.

In the language of the flattening stratification, for any closed `Z` (flat or not) the chart fibre
polynomial `fiberHilbertPolynomialAt ι g 𝒪_Z t` vanishes exactly when no point of `Z` lies over `t`
(`ProjectiveSpace.fiberHilbertPolynomialAt_quotientModule_eq_zero_iff`, `_ne_zero_iff`).

Present consumer: the surjectivity of `p : D ⟶ H` in the F16 quotient (plan task HQ11).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Cohomology

variable (ι : Type u)

section Field

variable {K : Type u} [Field K]

/-- **The empty closed subscheme of `P^n_K` has Hilbert polynomial `0`.** -/
theorem subschemeHilbertPolynomial_top : subschemeHilbertPolynomial ι K ⊤ = 0 :=
  Scheme.Cohomology.projectiveHilbertPolynomial_eq_zero_of_isZero K ι
    ((Scheme.IdealSheafData.isZero_quotientModule_iff _).mpr rfl)

/-- **A closed subscheme of `P^n_K` has zero Hilbert polynomial exactly when it is empty**, that is,
when its ideal sheaf is the unit ideal sheaf. -/
theorem subschemeHilbertPolynomial_eq_zero_iff (n : ℕ) (e : ι ≃ Fin (n + 1))
    (W : (ProjectiveSpace K ι).IdealSheafData) :
    subschemeHilbertPolynomial ι K W = 0 ↔ W = ⊤ := by
  have : Finite ι := Finite.of_equiv _ e.symm
  rw [← W.isZero_quotientModule_iff]
  exact Scheme.Cohomology.projectiveHilbertPolynomial_eq_zero_iff K ι n e
    W.affineLocallyFiniteType_quotientModule

/-- **A nonempty closed subscheme of `P^n_K` has nonzero Hilbert polynomial**, and conversely
(Nitsure, arXiv:math/0504590v1, proof of Thm 6.8, p. 33, used there without proof). -/
theorem subschemeHilbertPolynomial_ne_zero_iff (n : ℕ) (e : ι ≃ Fin (n + 1))
    (W : (ProjectiveSpace K ι).IdealSheafData) :
    subschemeHilbertPolynomial ι K W ≠ 0 ↔ Nonempty W.subscheme := by
  rw [W.nonempty_subscheme_iff, Ne, subschemeHilbertPolynomial_eq_zero_iff ι n e]

end Field

section Family

variable {A : Type u} [CommRing A] {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}

/-- **The fibre of a closed subscheme at a point is nonempty exactly when the point lies under the
subscheme**: for `Z ⊆ P^n_A ×_{Spec A} T` and a point `x : Spec K ⟶ T` (any ring `K`), the fibre
`Z.comap (pointMap ι g x) ⊆ P^n_K` has a point if and only if some point of `Spec K` and some
point of `Z` have the same image in `T`. `P^n_K` is the base change of `P^n_A ×_{Spec A} T ⟶ T`
along `x` (`isPullback_pointMap`), and the fibre is the base change of `Z`
(`IdealSheafData.comapIso`). -/
theorem nonempty_subscheme_comap_pointMap_iff {K : Type u} [CommRing K]
    (Z : (pullback (toSpec A ι) g).IdealSheafData) (x : Spec (CommRingCat.of K) ⟶ T) :
    Nonempty (Z.comap (pointMap ι g x)).subscheme ↔
      ∃ s, x s ∈ Set.range (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) := by
  constructor
  · rintro ⟨w⟩
    let p := (Z.comapIso (pointMap ι g x)).hom w
    refine ⟨toSpec K ι (pullback.fst (pointMap ι g x) Z.subschemeι p),
      pullback.snd (pointMap ι g x) Z.subschemeι p, ?_⟩
    have h1 : pullback.snd (pointMap ι g x) Z.subschemeι ≫ Z.subschemeι ≫
        pullback.snd (toSpec A ι) g =
          pullback.fst (pointMap ι g x) Z.subschemeι ≫ toSpec K ι ≫ x := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc, pointMap_snd]
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f p) h1
  · rintro ⟨s, z, hz⟩
    have hy : pullback.snd (toSpec A ι) g (Z.subschemeι z) = x s := by
      simpa only [Scheme.Hom.comp_apply] using hz
    obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback (Z.subschemeι z) s hy
    have hq' : pointMap ι g x ((isPullback_pointMap ι g x).isoPullback.inv q) =
        Z.subschemeι z := by
      have h := congrArg (fun f => f q) (isPullback_pointMap ι g x).isoPullback_inv_fst
      simp only [Scheme.Hom.comp_apply] at h
      exact h.trans hq
    obtain ⟨r, -, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hq'
    exact ⟨(Z.comapIso (pointMap ι g x)).inv r⟩

/-- **The fibre of a closed subscheme at a point `t` is nonempty exactly when `t` lies under the
subscheme**: for `Z ⊆ P^n_A ×_{Spec A} T` and `t ∈ T`, the fibre `Z_t ⊆ P^n_{κ(t)}` has a point if
and only if `t` is the image of a point of `Z`. No flatness and no Noetherian hypothesis. -/
theorem nonempty_subscheme_comap_fromSpecResidueField_iff
    (Z : (pullback (toSpec A ι) g).IdealSheafData) (t : T) :
    Nonempty (Z.comap (pointMap ι g (T.fromSpecResidueField t))).subscheme ↔
      t ∈ Set.range (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) := by
  refine (nonempty_subscheme_comap_pointMap_iff ι Z (T.fromSpecResidueField t)).trans ⟨?_, ?_⟩
  · rintro ⟨s, z, hz⟩
    exact ⟨z, hz.trans (Scheme.fromSpecResidueField_apply t s)⟩
  · rintro ⟨z, hz⟩
    obtain ⟨s⟩ : Nonempty (Spec (T.residueField t)) :=
      ⟨IsLocalRing.closedPoint (T.residueField t)⟩
    exact ⟨s, z, hz.trans (Scheme.fromSpecResidueField_apply t s).symm⟩

variable (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]} {Z : (pullback (toSpec A ι) g).IdealSheafData}

include e in
/-- **A family with nonzero Hilbert polynomial covers its base** (Nitsure, arXiv:math/0504590v1,
proof of Thm 6.8, p. 33, "Hence p : D → H is surjective"): if `Z` is a point of `Hilb^Φ(T)` with
`Φ ≠ 0`, then `Z ⟶ T` is surjective, since every fibre has Hilbert polynomial `Φ` and so is
nonempty. -/
theorem IsHilbertFamily.surjective_of_ne_zero (hZ : IsHilbertFamily ι Φ g Z) (hΦ : Φ ≠ 0) :
    Surjective (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) := by
  refine ⟨fun t => (nonempty_subscheme_comap_fromSpecResidueField_iff ι Z t).mp ?_⟩
  exact (subschemeHilbertPolynomial_ne_zero_iff ι n e _).mp fun h =>
    hΦ ((hZ.subschemeHilbertPolynomial_fiber _ (T.fromSpecResidueField t)).symm.trans h)

include e in
/-- **A nonempty family has nonzero Hilbert polynomial** (Nitsure, arXiv:math/0504590v1, proof of
Thm 6.8, p. 33: the fibres of `f₂` are nonempty, "and therefore the Hilbert polynomial of each fiber
is non-zero"): if `Z` is a point of `Hilb^Φ(T)` with a point, then `Φ ≠ 0`. -/
theorem IsHilbertFamily.ne_zero_of_nonempty (hZ : IsHilbertFamily ι Φ g Z)
    (hne : Nonempty Z.subscheme) : Φ ≠ 0 := by
  obtain ⟨z⟩ := hne
  have h := (subschemeHilbertPolynomial_ne_zero_iff ι n e _).mpr
    ((nonempty_subscheme_comap_fromSpecResidueField_iff ι Z
      ((Z.subschemeι ≫ pullback.snd (toSpec A ι) g) z)).mpr ⟨z, rfl⟩)
  exact fun hΦ => h ((hZ.subschemeHilbertPolynomial_fiber _ _).trans hΦ)

include e in
/-- Over a nonempty base, a point `Z` of `Hilb^Φ(T)` is surjective onto `T` exactly when
`Φ ≠ 0`. -/
theorem IsHilbertFamily.surjective_iff_ne_zero [Nonempty T] (hZ : IsHilbertFamily ι Φ g Z) :
    Surjective (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) ↔ Φ ≠ 0 := by
  refine ⟨fun h => hZ.ne_zero_of_nonempty ι n e ?_, hZ.surjective_of_ne_zero ι n e⟩
  obtain ⟨t⟩ := ‹Nonempty T›
  obtain ⟨z, -⟩ := h.surj t
  exact ⟨z⟩

include e in
/-- **The chart fibre polynomial vanishes exactly over the points not under the subscheme**: for a
closed subscheme `Z ⊆ P^n_A ×_{Spec A} T`, flat or not, and `t ∈ T`,
`fiberHilbertPolynomialAt ι g 𝒪_Z t = 0` if and only if no point of `Z` lies over `t`. The chart
polynomial is that of the fibre of `Z` at a residue field of an affine chart around `t`
(`fiberHilbertPolynomialAt_quotientModule_eq`). -/
theorem fiberHilbertPolynomialAt_quotientModule_eq_zero_iff
    (Z : (pullback (toSpec A ι) g).IdealSheafData) (t : T) :
    fiberHilbertPolynomialAt ι g Z.quotientModule t = 0 ↔
      t ∉ Set.range (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨U, hU, htU, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top t)
  have hx : ∀ s, (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U)
      (hU.primeIdealOf ⟨t, htU⟩).asIdeal.ResidueField)) ≫ hU.fromSpec) s = t := by
    intro s
    have hs : Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U)
        (hU.primeIdealOf ⟨t, htU⟩).asIdeal.ResidueField)) s = hU.primeIdealOf ⟨t, htU⟩ := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap Γ(T, U) (hU.primeIdealOf ⟨t, htU⟩).asIdeal.ResidueField)
        s.asIdeal = (hU.primeIdealOf ⟨t, htU⟩).asIdeal
      have := s.isPrime
      rw [Ideal.eq_bot_of_prime s.asIdeal, ← RingHom.ker_eq_comap_bot,
        Ideal.ker_algebraMap_residueField]
    rw [Scheme.Hom.comp_apply, hs, IsAffineOpen.fromSpec_primeIdealOf]
  rw [fiberHilbertPolynomialAt_quotientModule_eq ι hU t htU,
    subschemeHilbertPolynomial_eq_zero_iff ι n e, ← Scheme.IdealSheafData.isEmpty_subscheme_iff,
    ← not_nonempty_iff, nonempty_subscheme_comap_pointMap_iff]
  refine not_congr ⟨fun ⟨s, z, hz⟩ => ⟨z, hz.trans (hx s)⟩, fun ⟨z, hz⟩ =>
    ⟨IsLocalRing.closedPoint (hU.primeIdealOf ⟨t, htU⟩).asIdeal.ResidueField, z,
      hz.trans (hx _).symm⟩⟩

include e in
/-- The chart fibre polynomial of a closed subscheme is nonzero exactly at the points under the
subscheme. -/
theorem fiberHilbertPolynomialAt_quotientModule_ne_zero_iff
    (Z : (pullback (toSpec A ι) g).IdealSheafData) (t : T) :
    fiberHilbertPolynomialAt ι g Z.quotientModule t ≠ 0 ↔
      t ∈ Set.range (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) := by
  rw [Ne, fiberHilbertPolynomialAt_quotientModule_eq_zero_iff ι n e, not_not]

end Family

end AlgebraicGeometry.ProjectiveSpace
