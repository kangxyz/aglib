/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.PrincipalCoordinates
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Aglib.AlgebraicGeometry.Stalk.GenericFiber

/-!
# Principal open and closed coordinates on a DVR spectrum

The forward spectrum isomorphisms identify the actual fraction and residue maps.
This extracts the scheme geometry of `R5Lab.Aglib.AlgebraicGeometry.Stalk.DVRCoordinates`
at R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, using literal quotient rings
and localization maps rather than importing a module-sheaf specialization.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open IsDiscreteValuationRing.PrincipalCoordinates

namespace AlgebraicGeometry.Scheme.Spec.DiscreteValuationRing

universe u

variable (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {π : R} (hπ : Irreducible π)

/-- The spectrum of the original fraction field is the principal open spectrum. -/
def genericIso : Spec (CommRingCat.of K) ≅
    Spec (CommRingCat.of (Localization.Away π)) :=
  Scheme.Spec.mapIso (awayFractionEquiv R K hπ).toRingEquiv.toCommRingCatIso.op

/-- The spectrum of the original residue field is the principal closed spectrum. -/
def closedIso : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ≅
    Spec (CommRingCat.of (R ⧸ Ideal.span {π})) :=
  Scheme.Spec.mapIso (closedResidueEquiv R hπ).toCommRingCatIso.op

/-- The original fraction-ring map is the transported localization map. -/
theorem genericIso_open_triangle :
    (genericIso R K hπ).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away π))) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  change Spec.map (CommRingCat.ofHom (awayFractionEquiv R K hπ).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away π))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, awayFractionEquiv_comp_algebraMap]

/-- The original residue map is the transported principal quotient map. -/
theorem closedIso_closed_triangle :
    (closedIso R hπ).hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π}))) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
  change Spec.map (CommRingCat.ofHom (closedResidueEquiv R hπ).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π}))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, closedResidueEquiv_comp_quotient]

end AlgebraicGeometry.Scheme.Spec.DiscreteValuationRing
