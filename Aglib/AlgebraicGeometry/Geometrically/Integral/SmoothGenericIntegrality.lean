/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothGenericSpreading
public import Aglib.AlgebraicGeometry.Spec.OpenMapPrincipalFibres

/-! # Principal geometric integrality of the original smooth family

The original open-image principal shrink supplies nonempty field fibres.
Combining it with the original common-open and density shrink gives geometric
integrality on one actual principal base change. No section, surjectivity,
properness, or perfectness hypothesis is added. The base remains Noetherian;
relative component-locus openness is a separate theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- The original smooth family has integral fibres over every field map on
one nonzero principal base open. Fibre nonemptiness is proved from the
original open image, not assumed. -/
theorem exists_ne_zero_integral_smooth_field_pullbacks
    (R K Ω : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [QuasiCompact f] [QuasiSeparated f]
    [GeometricallyIntegral (pullback.snd f (Spec.algebraMap R K))] :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type u) [Field L] [Algebra R L],
      algebraMap R L r ≠ 0 → IsIntegral (pullback f (Spec.algebraMap R L)) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsIntegral (pullback f (Spec.algebraMap R K)) :=
    GeometricallyIntegral.isIntegral_of_subsingleton
      (pullback.snd f (Spec.algebraMap R K))
  let : Nonempty X :=
    ⟨pullback.fst f (Spec.algebraMap R K) (Classical.choice inferInstance)⟩
  obtain ⟨r, hr, hi⟩ := exists_ne_zero_integral_nonempty_smooth_fibres R K Ω f n
  obtain ⟨s, hs, hn⟩ := exists_ne_zero_nonempty_field_pullbacks_of_isOpenMap R f f.isOpenMap
  refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
  intro L _ _ hrs
  have hrL : algebraMap R L r ≠ 0 := by
    intro h
    exact hrs (by rw [map_mul, h, zero_mul])
  have hsL : algebraMap R L s ≠ 0 := by
    intro h
    exact hrs (by rw [map_mul, h, mul_zero])
  exact hi L hrL (hn L hsL)

/-- Generic geometric integrality of a smooth quasi-compact quasi-separated
family over a Noetherian domain spreads to its actual principal base change.
The original fraction field, family, and base-change structural maps remain
unchanged. This is not the relative section-component openness theorem. -/
theorem exists_ne_zero_geometricallyIntegral_smooth_principal
    (R K Ω : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [QuasiCompact f] [QuasiSeparated f]
    [GeometricallyIntegral (pullback.snd f (Spec.algebraMap R K))] :
    ∃ r : R, r ≠ 0 ∧ GeometricallyIntegral
      (pullback.snd f (Spec.algebraMap R (Localization.Away r))) := by
  obtain ⟨r, hr, h⟩ := exists_ne_zero_integral_smooth_field_pullbacks R K Ω f n
  refine ⟨r, hr, ?_⟩
  let b := Spec.algebraMap R (Localization.Away r)
  let : ObjectProperty.IsClosedUnderIsomorphisms (IsIntegral : Scheme.{u} → Prop) :=
    ⟨fun e hi => by
      let := hi
      exact IsIntegral.of_isIso e.hom⟩
  constructor
  refine (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := IsIntegral) (R := Localization.Away r) (f := pullback.snd f b)).mpr ?_
  intro L _ _
  let : Algebra R L := ((algebraMap (Localization.Away r) L).comp
    (algebraMap R (Localization.Away r))).toAlgebra
  let : IsScalarTower R (Localization.Away r) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hrL : algebraMap R L r ≠ 0 := by
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).map
      (algebraMap (Localization.Away r) L)
    exact hu.ne_zero
  let s := Spec.algebraMap (Localization.Away r) L
  have hs : s ≫ b = Spec.algebraMap R L := by
    rw [← Spec.map_comp]
    congr 1
  have hj : IsIntegral (pullback f (s ≫ b) : Scheme.{u}) := by
    rw [hs]
    exact h L hrL
  let := hj
  exact IsIntegral.of_isIso (pullbackLeftPullbackSndIso f b s).inv

end AlgebraicGeometry.Scheme
