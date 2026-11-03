/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.RingTheory.Excellent.GeometricConditions

/-! # Finite singular sets on original affine opens

The actual affine/stalk comparison is extracted from the surface singular-locus
proof. The ring regular-locus complement is the only finiteness input.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- Finiteness of the regular-locus complement of an original affine section
ring gives finiteness of the singular scheme points in that affine open. -/
theorem finite_singularSet_inter_affine_of_finite_compl_regularLocus
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (hfin : (PrimeSpectrum.regularLocus Γ(X, U))ᶜ.Finite) :
    {x : X | x ∈ U ∧ ¬ IsRegularLocalRing (X.presheaf.stalk x)}.Finite := by
  apply (hfin.image hU.fromSpec).subset
  rintro x ⟨hxU, hx⟩
  have hxrange : x ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hxU
  obtain ⟨p, hp⟩ := hxrange
  refine ⟨p, ?_, hp⟩
  intro hreg
  let : p.asIdeal.IsPrime := p.isPrime
  let : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hreg
  let : IsRegularLocalRing ((Spec Γ(X, U)).presheaf.stalk p) :=
    IsRegularLocalRing.of_ringEquiv (Spec.stalkIso Γ(X, U) p).commRingCatIsoToRingEquiv.symm
  have hr : IsRegularLocalRing (X.presheaf.stalk (hU.fromSpec p)) :=
    IsRegularLocalRing.of_ringEquiv
      (asIso (hU.fromSpec.stalkMap p)).symm.commRingCatIsoToRingEquiv
  exact hx (hp ▸ hr)

end AlgebraicGeometry.Scheme
