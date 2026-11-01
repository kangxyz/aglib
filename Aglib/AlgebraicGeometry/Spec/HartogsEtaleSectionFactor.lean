/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsClopenExtension
public import Aglib.AlgebraicGeometry.Spec.ScalarIsoReflection
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NativeScalarSections
public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.Immersions
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Flat.Localization

/-! # Extending the actual finite-etale section factor across Hartogs opens

The section image gives an original idempotent. Its canonical localization
is an isomorphic component of the unchanged affine algebra. Only the two
original scalar-section identifications are used; normality after base
change, a chosen normalization, and effectivity of arbitrary covers are absent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- The literal section factor of a finite-etale comparison extends to an
idempotent factor of the original affine map, and that factor is an isomorphism. -/
theorem exists_idempotent_sectionFactor_isIso
    {B C : Type u} [CommRing B] [CommRing C] {X Y : Scheme.{u}}
    (α : X ⟶ Spec (.of B)) (β : Y ⟶ Spec (.of C))
    [QuasiCompact β] [QuasiSeparated β]
    (τ : B →+* C) (r : Y ⟶ X) [IsFinite r] [Etale r]
    (h : r ≫ α = β ≫ Spec.map (CommRingCat.ofHom τ))
    (hα : Function.Bijective (affineScalarMap α))
    (hβ : Function.Bijective (affineScalarMap β))
    (s : X ⟶ Y) (hs : s ≫ r = 𝟙 X) :
    ∃ e : C, IsIdempotentElem e ∧
      β ⁻¹' ((PrimeSpectrum.basicOpen e).carrier : Set (Spec (.of C))) =
        Set.range s ∧
      IsIso (Spec.algebraMap C (Localization.Away e) ≫
        Spec.map (CommRingCat.ofHom τ)) := by
  let : IsFinite (s ≫ r) := by rw [hs]; infer_instance
  let : IsFinite s := IsFinite.of_comp s r
  let : IsOpenImmersion s := IsOpenImmersion.of_section_formallyUnramified s r hs
  obtain ⟨e, he, hpre⟩ := exists_idempotent_basicOpen_preimage_eq_of_affineScalar_bijective
    β hβ s.opensRange s.isClosedMap.isClosed_range
  have heSet : β ⁻¹' ((PrimeSpectrum.basicOpen e).carrier : Set (Spec (.of C))) =
        Set.range s :=
    congrArg (fun U : Y.Opens => (U : Set Y)) hpre
  refine ⟨e, he, heSet, ?_⟩
  let loc := Spec.algebraMap C (Localization.Away e)
  let j := pullback.fst β loc
  let q := pullback.snd β loc
  have hloc : Set.range loc =
      ((PrimeSpectrum.basicOpen e).carrier : Set (Spec (.of C))) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away e) e
  have hj : Set.range j = Set.range s := by
    rw [show Set.range j = β ⁻¹' Set.range loc from Pullback.range_fst β loc, hloc]
    exact heSet
  let E := IsOpenImmersion.isoOfRangeEq j s hj
  have hE : E.hom ≫ s = j := IsOpenImmersion.isoOfRangeEq_hom_fac j s hj
  have hfactor : j ≫ r = E.hom := by
    rw [← hE, Category.assoc, hs, Category.comp_id]
  let : IsIso (j ≫ r) := by rw [hfactor]; infer_instance
  have hq : Function.Bijective (affineScalarMap q) :=
    Cohomology.scalarSections_bijective_of_flat_of_isPullback j
      (algebraMap C (Localization.Away e)) q β (IsPullback.of_hasPullback β loc)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) hβ
  let σ : B →+* Localization.Away e := (algebraMap C (Localization.Away e)).comp τ
  have hσ : Spec.map (CommRingCat.ofHom σ) = loc ≫ Spec.map (CommRingCat.ofHom τ) :=
    Spec.map_comp (CommRingCat.ofHom τ) (CommRingCat.ofHom (algebraMap C (Localization.Away e)))
  have H : (j ≫ r) ≫ α = q ≫ Spec.map (CommRingCat.ofHom σ) := by
    rw [Category.assoc, h, ← Category.assoc, pullback.condition, Category.assoc, hσ]
  have hi := isIso_specMap_of_affineScalarSquare (j ≫ r) q α σ H hα hq.injective
  rw [hσ] at hi
  exact hi

end AlgebraicGeometry.Scheme
