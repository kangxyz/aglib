/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.At
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Original affine pointwise etaleness

The open-neighbourhood definition and the native ring-theoretic etale locus
agree for the original finitely presented algebra map. Both directions use
actual principal localizations; no alternate stalk realization is selected.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The original principal-localization triangle on spectra. -/
theorem specAlgebraMap_away_comp (b : S) :
    Spec.algebraMap S (Localization.Away b) ≫ Spec.algebraMap R S =
      Spec.algebraMap R (Localization.Away b) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- Etaleness on an original source neighbourhood agrees with the actual algebraic
etale locus for a finitely presented algebra. -/
theorem specAlgebraMap_etaleAt_iff [Algebra.FinitePresentation R S]
    (q : PrimeSpectrum S) :
    (Spec.algebraMap R S).etaleAt q ↔ Algebra.IsEtaleAt R q.asIdeal := by
  constructor
  · rintro ⟨U, hq, hU⟩
    let : Etale (U.ι ≫ Spec.algebraMap R S) := hU
    obtain ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, hqb, hbU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hq U.isOpen
    let l := Spec.algebraMap S (Localization.Away b)
    have hlU : Set.range l ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      change (l.opensRange : Set (Spec (.of S))) ⊆ (U : Set (Spec (.of S)))
      have hrange : l.opensRange = PrimeSpectrum.basicOpen b :=
        Hom.opensRange_localizationAway (R := CommRingCat.of S) b
      exact (congrArg (fun V : (Spec (.of S)).Opens =>
        (V : Set (Spec (.of S))) ⊆ (U : Set (Spec (.of S)))) hrange).mpr hbU
    let j := IsOpenImmersion.lift U.ι l hlU
    let : IsOpenImmersion j := inferInstance
    have hlf : Etale (l ≫ Spec.algebraMap R S) := by
      rw [← IsOpenImmersion.lift_fac U.ι l hlU, Category.assoc]
      infer_instance
    have hspec : Etale (Spec.algebraMap R (Localization.Away b)) := by
      rw [← specAlgebraMap_away_comp (R := R) b]
      exact hlf
    have hring : Algebra.Etale R (Localization.Away b) :=
      RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hspec)
    exact (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr hring) hqb
  · intro hq
    let : Algebra.IsEtaleAt R q.asIdeal := hq
    obtain ⟨b, hb, hBb⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) q.asIdeal
    let : Algebra.Etale R (Localization.Away b) := hBb
    let l := Spec.algebraMap S (Localization.Away b)
    have hl : Etale (l ≫ Spec.algebraMap R S) := by
      rw [specAlgebraMap_away_comp]
      exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hBb)
    let : Etale (l ≫ Spec.algebraMap R S) := hl
    have hql : q ∈ l.opensRange := by
      have hrange : l.opensRange = PrimeSpectrum.basicOpen b :=
        Hom.opensRange_localizationAway (R := CommRingCat.of S) b
      exact (congrArg (fun V : (Spec (.of S)).Opens => q ∈ V) hrange).mpr hb
    let e := IsOpenImmersion.isoOfRangeEq l l.opensRange.ι (by simp)
    refine ⟨l.opensRange, hql, ?_⟩
    have he : e.inv ≫ (l ≫ Spec.algebraMap R S) =
        l.opensRange.ι ≫ Spec.algebraMap R S := by
      rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac]
    rw [← he]
    infer_instance

end AlgebraicGeometry.Scheme.Hom
