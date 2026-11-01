/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteGenericModel
public import Aglib.AlgebraicGeometry.Morphisms.Etale.FiniteGenericNeighborhood
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Actual finite etale models of a generic finite etale cover -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.FinitePresentationDescent

universe u

/-- An actual affine open model, with its original generic cartesian comparison. -/
structure FiniteEtaleGenericModel (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K)) where
  /-- The actual affine open base. -/
  base : Scheme.{u}
  /-- Its original inclusion into the original spectrum. -/
  inclusion : base ⟶ Spec (.of R)
  /-- Affineness of the actual base. -/
  affine : IsAffine base
  /-- The original inclusion is open. -/
  openImmersion : IsOpenImmersion inclusion
  /-- The original fraction-field point on the open base. -/
  point : Spec (.of K) ⟶ base
  /-- Its literal structural triangle. -/
  point_over : point ≫ inclusion = Spec.map (CommRingCat.ofHom (algebraMap R K))
  /-- The actual cartesian finite-presentation model. -/
  model : Model point f
  /-- The model map is finite. -/
  finite : IsFinite model.f
  /-- The same model map is etale. -/
  etale : Etale model.f

attribute [instance] FiniteEtaleGenericModel.affine FiniteEtaleGenericModel.openImmersion
  FiniteEtaleGenericModel.finite FiniteEtaleGenericModel.etale

/-- A finite etale scheme over the fraction field of a Noetherian domain has an
actual finite etale model on a nonempty affine open of the original spectrum.
The model retains the original generic scheme, not just an abstract field algebra. -/
def finiteEtaleGenericModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    FiniteEtaleGenericModel R K f := by
  apply Classical.choice
  obtain ⟨r, hr, v, hv, M, hM⟩ := exists_finiteModel_over_principalLocalization R K f
  let S := Localization.Away r
  have : IsDomain S := Localization.Away.isDomain hr
  let : Algebra S K := v.toRingHom.toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algHom v
  have : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r) S K
  have : IsFinite M.f := hM
  let π : Spec (.of K) ⟶ Spec (.of S) := Spec.map (CommRingCat.ofHom v.toRingHom)
  have het : Etale (pullback.snd M.f π) := by
    have : Etale (M.square.isoPullback.inv ≫ f) := inferInstance
    simpa only [IsPullback.isoPullback_inv_snd] using this
  obtain ⟨U, hUa, hU, he⟩ :=
    exists_affine_etale_neighborhood_of_fractionField_baseChange (.of S) K M.f het
  have hpoint (x : Spec (.of K)) : π x = genericPoint (Spec (.of S)) := by
    change PrimeSpectrum.comap v.toRingHom x = genericPoint (Spec (.of S))
    rw [genericPoint_eq_bot_of_affine, Subsingleton.elim x (⊥ : PrimeSpectrum K)]
    apply PrimeSpectrum.ext
    exact (RingHom.injective_iff_ker_eq_bot v.toRingHom).mp hv
  have hrange : Set.range π ⊆ Set.range U.ι := by
    rintro x ⟨z, rfl⟩
    rw [Opens.range_ι]
    rw [hpoint z]
    exact hU
  let q := IsOpenImmersion.lift U.ι π hrange
  have hq : q ≫ U.ι = π := IsOpenImmersion.lift_fac _ _ _
  let N := M.factorBase q U.ι hq
  have : IsFinite N.f := inferInstanceAs (IsFinite (pullback.snd M.f U.ι))
  have : Etale N.f := by
    change Etale (pullback.snd M.f U.ι)
    let H := (isPullback_morphismRestrict M.f U).flip
    have : Etale (M.f ∣_ U) := he
    have : Etale (H.isoPullback.inv ≫ (M.f ∣_ U)) := inferInstance
    simpa only [IsPullback.isoPullback_inv_snd] using this
  refine ⟨{
    base := U
    inclusion := U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))
    affine := hUa
    openImmersion := inferInstance
    point := q
    point_over := ?_
    model := N
    finite := inferInstance
    etale := inferInstance }⟩
  rw [← Category.assoc, hq, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext v.comp_algebraMap)

end AlgebraicGeometry.Scheme.FinitePresentationDescent
