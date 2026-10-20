/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.FractionAway
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Principal coordinates for a discrete valuation ring

The principal open at an irreducible element has the original fraction field,
and the principal closed quotient has the original residue field. The equations
identify the actual algebra and quotient maps. These are the algebraic parts of
`R5Lab.Aglib.RingTheory.DiscreteValuationRing.PrincipalCoordinates` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`; no scheme-module import is needed.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing.PrincipalCoordinates

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  {π : R} (hπ : Irreducible π)

/-- The specified fraction field is the actual localization at the chosen element. -/
def awayFractionEquiv : Localization.Away π ≃ₐ[R] K :=
  letI := IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit K
    hπ.ne_zero hπ.not_isUnit
  IsLocalization.algEquiv (Submonoid.powers π) (Localization.Away π) K

/-- The forward fraction-field equivalence preserves the original algebra map. -/
theorem awayFractionEquiv_comp_algebraMap :
    (awayFractionEquiv R K hπ).toRingHom.comp (algebraMap R (Localization.Away π)) =
      algebraMap R K := by
  ext r
  exact (awayFractionEquiv R K hπ).commutes r

/-- The literal principal quotient is the local residue field. -/
def closedResidueEquiv : (R ⧸ Ideal.span {π}) ≃+* IsLocalRing.ResidueField R :=
  Ideal.quotEquivOfEq hπ.maximalIdeal_eq.symm

/-- The forward quotient equivalence preserves the original residue map. -/
theorem closedResidueEquiv_comp_quotient :
    (closedResidueEquiv R hπ).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {π})) =
      IsLocalRing.residue R := by
  ext r
  exact Ideal.quotEquivOfEq_mk hπ.maximalIdeal_eq.symm r

end IsDiscreteValuationRing.PrincipalCoordinates
