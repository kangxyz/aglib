/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Fibre
public import Aglib.AlgebraicGeometry.Spec.Localization
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.Restriction
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.Locality
public import Aglib.RingTheory.Flat.PrincipalQuotient.Fibrewise
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Invertible ideals of finite flat subschemes in smooth relative curves

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open TensorProduct
open LinearMap
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Hom

/-- The affine lifting step reduced to regularity of the already lifted
principal generators. This conditional helper does not assert that criterion. -/
theorem smoothSpectralIdeal_rankOne_of_principalRegular
    {R A B : CommRingCat.{u}} (ψ : R ⟶ A) (φ : A ⟶ B)
    [SmoothOfRelativeDimension 1 (Spec.map ψ)] [IsClosedImmersion (Spec.map φ)]
    [LocallyQuasiFinite (Spec.map φ ≫ Spec.map ψ)]
    [Flat (Spec.map φ ≫ Spec.map ψ)]
    [LocallyOfFinitePresentation (Spec.map φ ≫ Spec.map ψ)]
    (hreg : ∀ (s : A) (a : RingHom.ker φ.hom),
      (RingHom.ker φ.hom).map (algebraMap A (Localization.Away s)) =
        Ideal.span {algebraMap A (Localization.Away s) a.val} →
      IsSMulRegular (Localization.Away s) (algebraMap A (Localization.Away s) a.val)) :
    IsLocallyRankOne (Spec A) (idealModule (Spec.map φ)) := by
  have : Smooth (Spec.map ψ) := SmoothOfRelativeDimension.smooth 1 _
  apply affineIdeal_rankOne_of_localizedBasis φ
  intro P
  obtain ⟨s, hs, a, ha⟩ := exists_away_surjective_idealGenerator (Spec.map ψ) φ
    (spectralIdeal_fg ψ φ) P.asIdeal
  have hspan := _root_.Ideal.idealMap_eq_span_of_localized_surjective (RingHom.ker φ.hom) (.powers
    s) a ha
  let b := _root_.Ideal.regularPrincipalIdealBasis
    ((RingHom.ker φ.hom).map (algebraMap A (Localization.Away s)))
    (algebraMap A (Localization.Away s) a.val) (hreg s a hspan) hspan
  let e := (IsLocalizedModule.iso (.powers s)
    (Algebra.idealMap (Localization.Away s) (RingHom.ker φ.hom))).extendScalarsOfIsLocalization
      (.powers s) (Localization.Away s)
  exact ⟨s, hs, ⟨b.map e.symm⟩⟩

private theorem idealModule_isLocallyRankOne_affine_of_spectral
    (h : ∀ (R A B : CommRingCat.{u}) (ψ : R ⟶ A) (φ : A ⟶ B),
      SmoothOfRelativeDimension 1 (Spec.map ψ) → IsClosedImmersion (Spec.map φ) →
        LocallyQuasiFinite (Spec.map φ ≫ Spec.map ψ) →
          Flat (Spec.map φ ≫ Spec.map ψ) →
            LocallyOfFinitePresentation (Spec.map φ ≫ Spec.map ψ) →
              IsLocallyRankOne (Spec A) (idealModule (Spec.map φ)))
    {S X D : Scheme.{u}} [IsAffine S] [IsAffine X]
    (p : X ⟶ S) (i : D ⟶ X) [SmoothOfRelativeDimension 1 p]
    [IsClosedImmersion i] [LocallyQuasiFinite (i ≫ p)] [Flat (i ≫ p)]
    [LocallyOfFinitePresentation (i ≫ p)] :
    IsLocallyRankOne X (idealModule i) := by
  let : IsAffine D := isAffine_of_isAffineHom i
  have hp : SmoothOfRelativeDimension 1 (Spec.map p.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff (@SmoothOfRelativeDimension.{u} 1)
      (arrowIsoSpecΓOfIsAffine p)).mp inferInstance
  have hi : IsClosedImmersion (Spec.map i.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion.{u}
      (arrowIsoSpecΓOfIsAffine i)).mp inferInstance
  have hq : LocallyQuasiFinite (Spec.map i.appTop ≫ Spec.map p.appTop) := by
    rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop]
    exact (MorphismProperty.arrow_mk_iso_iff @LocallyQuasiFinite.{u}
      (arrowIsoSpecΓOfIsAffine (i ≫ p))).mp inferInstance
  have hf : Flat (Spec.map i.appTop ≫ Spec.map p.appTop) := by
    rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop]
    exact (MorphismProperty.arrow_mk_iso_iff @Flat.{u}
      (arrowIsoSpecΓOfIsAffine (i ≫ p))).mp inferInstance
  have hl : LocallyOfFinitePresentation (Spec.map i.appTop ≫ Spec.map p.appTop) := by
    rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop]
    exact (MorphismProperty.arrow_mk_iso_iff @LocallyOfFinitePresentation.{u}
      (arrowIsoSpecΓOfIsAffine (i ≫ p))).mp inferInstance
  have hSpec := h Γ(S, ⊤) Γ(X, ⊤) Γ(D, ⊤) p.appTop i.appTop hp hi hq hf hl
  have := idealPullbackMap_isIso_of_iso_square
    (Spec.map i.appTop) i X.isoSpec.hom D.isoSpec.hom (Scheme.isoSpec_hom_naturality i)
  exact isLocallyRankOne_of_iso X (asIso (idealPullbackMap
    (Spec.map i.appTop) i X.isoSpec.hom D.isoSpec.hom (Scheme.isoSpec_hom_naturality i)))
      (pullback_locallyRankOne X.isoSpec.hom _ hSpec)

/-- Conditional globalization from the displayed spectral ideal criterion. Local quasi-finiteness is
retained at the
spectral boundary because restricting an ambient affine open need not preserve
finiteness. This theorem does not prove the spectral hypothesis. -/
theorem idealModule_isLocallyRankOne_of_spectral
    (h : ∀ (R A B : CommRingCat.{u}) (ψ : R ⟶ A) (φ : A ⟶ B),
      SmoothOfRelativeDimension 1 (Spec.map ψ) → IsClosedImmersion (Spec.map φ) →
        LocallyQuasiFinite (Spec.map φ ≫ Spec.map ψ) →
          Flat (Spec.map φ ≫ Spec.map ψ) →
            LocallyOfFinitePresentation (Spec.map φ ≫ Spec.map ψ) →
              IsLocallyRankOne (Spec A) (idealModule (Spec.map φ))) :
    (∀ (S X D : Scheme.{u}) (p : X ⟶ S) (i : D ⟶ X),
    SmoothOfRelativeDimension 1 p → IsClosedImmersion i →
      IsFinite (i ≫ p) → Flat (i ≫ p) → LocallyOfFinitePresentation (i ≫ p) →
        IsLocallyRankOne X (idealModule i)) := by
  intro S X D p i hp hi hfin hf hl
  let := hp
  let := hi
  let := hfin
  let := hf
  let := hl
  have hloc : ∀ x : X, ∃ (U : S.Opens) (_ : IsAffineOpen U)
      (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧ V ≤ p ⁻¹ᵁ U := by
    intro x
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show p x ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ p ⁻¹ᵁ U from hxU)
    exact ⟨U, hU, V, hV, hxV, hVU⟩
  choose U hU V hV hxV hVU using hloc
  have hcover : IsOpenCover V := .mk (by
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxV x⟩)
  apply isLocallyRankOne_of_cover_restrict (idealModule i) V hcover
  intro x
  let : IsAffine (U x).toScheme := hU x
  let : IsAffine (V x).toScheme := hV x
  let : SmoothOfRelativeDimension 1 (p ∣_ U x) :=
    IsZariskiLocalAtTarget.restrict (P := @SmoothOfRelativeDimension.{u} 1) hp (U x)
  let : SmoothOfRelativeDimension 1 (p.resLE (U x) (V x) (hVU x)) := by
    delta Scheme.Hom.resLE
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  have hcomp : (i ∣_ V x) ≫ p.resLE (U x) (V x) (hVU x) =
      (i ≫ p).resLE (U x) (i ⁻¹ᵁ V x) (by
        rw [Scheme.Hom.comp_preimage]
        exact i.preimage_mono (hVU x)) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
  let : LocallyQuasiFinite ((i ∣_ V x) ≫ p.resLE (U x) (V x) (hVU x)) := by
    rw [hcomp]
    infer_instance
  let : Flat ((i ∣_ V x) ≫ p.resLE (U x) (V x) (hVU x)) := by
    rw [hcomp]
    infer_instance
  let : LocallyOfFinitePresentation ((i ∣_ V x) ≫ p.resLE (U x) (V x) (hVU x)) := by
    rw [hcomp]
    infer_instance
  exact isLocallyRankOne_of_iso (V x).toScheme (idealRestrictionIso i (V x)).symm
    (idealModule_isLocallyRankOne_affine_of_spectral h
      (p.resLE (U x) (V x) (hVU x)) (i ∣_ V x))

/-- Conditional assembly of the original smooth-divisor family from the
all-base residue-field regularity criterion. -/
theorem idealModule_isLocallyRankOne_of_residueCriterion
    (hreg : ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
      [Module.Flat R A] [Algebra.FinitePresentation R A] (a : A),
      (∀ (P : Ideal R) [P.IsPrime],
        IsSMulRegular (P.ResidueField ⊗[R] A) ((1 : P.ResidueField) ⊗ₜ[R] a)) →
        IsSMulRegular A a) : (∀ (S X D : Scheme.{u}) (p : X ⟶ S) (i : D ⟶ X),
    SmoothOfRelativeDimension 1 p → IsClosedImmersion i →
      IsFinite (i ≫ p) → Flat (i ≫ p) → LocallyOfFinitePresentation (i ≫ p) →
        IsLocallyRankOne X (idealModule i)) := by
  apply idealModule_isLocallyRankOne_of_spectral
  intro R A B ψ φ hp hi hq hf hl
  let := hp
  let := hi
  let := hq
  let := hf
  let := hl
  apply smoothSpectralIdeal_rankOne_of_principalRegular ψ φ
  intro s a hspan
  let : SmoothOfRelativeDimension 1
      (Spec.map (ψ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away s)))) := by
    rw [Spec.map_comp]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  let := _root_.AlgebraicGeometry.Scheme.isClosedImmersion_specMap_localizationAway φ s
  let := _root_.AlgebraicGeometry.Scheme.locallyQuasiFinite_specMap_localizationAway_comp ψ φ s
  let := _root_.AlgebraicGeometry.Scheme.flat_specMap_localizationAway_comp ψ φ s
  exact smoothPrincipalKernel_regular_of_residueCriterion hreg
    ((ψ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away s)))) ((CommRingCat.ofHom
      (IsLocalization.Away.map (Localization.Away s) (Localization.Away (φ s)) φ.hom s)))
    (algebraMap A (Localization.Away s) a.val)
    ((CommRingCat.ker_localizationAway_map φ s).trans hspan)

/-- The unchanged smooth relative divisor ideal interface over arbitrary bases. -/
theorem idealModule_isLocallyRankOne_of_smooth_of_finite_flat : (∀ (S X D : Scheme.{u}) (p : X ⟶ S)
  (i : D ⟶ X),
    SmoothOfRelativeDimension 1 p → IsClosedImmersion i →
      IsFinite (i ≫ p) → Flat (i ≫ p) → LocallyOfFinitePresentation (i ≫ p) →
        IsLocallyRankOne X (idealModule i)) := by
  apply idealModule_isLocallyRankOne_of_residueCriterion
  intro R A _ _ _ _ _ a ha
  exact (_root_.Algebra.regular_and_flat_of_fibre_regular a ha).1

end AlgebraicGeometry.Scheme.Hom
end
