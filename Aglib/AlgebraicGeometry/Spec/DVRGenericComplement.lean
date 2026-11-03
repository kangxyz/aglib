/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.FractionAway
public import Aglib.AlgebraicGeometry.Stalk.SpecLocalRing
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # The original DVR generic fibre at a target stalk

The supplied original fraction field is a localization at the uniformizer.
Its canonical map to the actual principal-open stalk ring gives the original
localization pushout. Pullback cancellation then identifies the principal
open with the restriction of the original generic fibre, with both actual
projection maps retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type u} [CommRing B] (φ : R →+* B) (t : R) (ht : Irreducible t)

/-- The canonical localization map from the original fraction field to the
principal-open ring of the original scalar image. -/
def dvrFractionParameterMap : K →+* Localization.Away (φ t) :=
  letI := IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit K
    ht.ne_zero ht.not_isUnit
  IsLocalization.Away.map K (Localization.Away (φ t)) φ t

/-- The entire original scalar square commutes. -/
theorem dvrFractionParameterMap_comp :
    (dvrFractionParameterMap R K φ t ht).comp (algebraMap R K) =
      (algebraMap B (Localization.Away (φ t))).comp φ := by
  let : IsLocalization.Away t K :=
    IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit K ht.ne_zero ht.not_isUnit
  exact IsLocalization.map_comp (M := Submonoid.powers t)
    (T := Submonoid.powers (φ t)) (S := K) (Q := Localization.Away (φ t)) (g := φ)
    (by
      rintro a ⟨n, rfl⟩
      exact ⟨n, (map_pow φ t n).symm⟩)

/-- The original field and principal-open maps form the canonical Cartesian square. -/
theorem dvrFractionParameterMap_isPullback :
    IsPullback (Spec.algebraMap B (Localization.Away (φ t)))
      (Spec.map (CommRingCat.ofHom (dvrFractionParameterMap R K φ t ht)))
      (Spec.map (CommRingCat.ofHom φ)) (Spec.algebraMap R K) := by
  let : IsLocalization.Away t K :=
    IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit K ht.ne_zero ht.not_isUnit
  let : IsLocalization ((Submonoid.powers t).map φ) (Localization.Away (φ t)) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R K))
    (CommRingCat.ofHom (algebraMap B (Localization.Away (φ t))))
    (CommRingCat.ofHom (dvrFractionParameterMap R K φ t ht))
    (CommRingCat.isPushout_of_isLocalization φ (dvrFractionParameterMap R K φ t ht)
      (dvrFractionParameterMap_comp R K φ t ht) (Submonoid.powers t))

/-- The actual principal open of the original target stalk is the restriction
of the original generic fibre. No smoothness or local finite presentation
of the stalk map is asserted or required. -/
theorem exists_dvrGenericStalk_complement
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (x : X) :
    ∃ g : Spec (.of (Localization.Away (p.stalkScalar x t))) ⟶
        pullback p (Spec.algebraMap R K),
      IsPullback g (Spec.algebraMap (X.presheaf.stalk x)
        (Localization.Away (p.stalkScalar x t)))
        (pullback.fst p (Spec.algebraMap R K)) (X.fromSpecStalk x) ∧
      g ≫ pullback.snd p (Spec.algebraMap R K) =
        Spec.map (CommRingCat.ofHom (dvrFractionParameterMap R K (p.stalkScalar x) t ht)) := by
  let j := Spec.algebraMap (X.presheaf.stalk x) (Localization.Away (p.stalkScalar x t))
  let a := Spec.map (CommRingCat.ofHom (dvrFractionParameterMap R K (p.stalkScalar x) t ht))
  have H := (dvrFractionParameterMap_isPullback R K (p.stalkScalar x) t ht).flip
  have H' : IsPullback a j (Spec.algebraMap R K) (X.fromSpecStalk x ≫ p) := by
    rw [fromSpecStalk_comp_eq_spec_map_stalkScalar]
    exact H
  let g := pullback.lift (j ≫ X.fromSpecStalk x) a (by
    rw [Category.assoc]
    exact H'.w.symm)
  have hg : g ≫ pullback.snd p (Spec.algebraMap R K) = a := pullback.lift_snd ..
  refine ⟨g, ?_, hg⟩
  apply IsPullback.of_right (h₁₂ := pullback.snd p (Spec.algebraMap R K))
    (h₂₂ := p) _ (pullback.lift_fst ..) (IsPullback.of_hasPullback p (Spec.algebraMap R K)).flip
  rw [hg]
  exact H'

end AlgebraicGeometry.Scheme
