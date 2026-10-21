/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterLocalization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The actual residue field of the parameter localization

Reduction of polynomial coefficients identifies the residue field of the native
localization at `(C p)` with the fraction field of the polynomial ring over the
original residue field. No finiteness assumption on the variables is needed.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace ParameterLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v) (p : R) [Fact (Irreducible p)]

attribute [local instance] algebraMap_isLocalHom

/-- Coefficient reduction has exactly the actual parameter prime as kernel. -/
theorem ker_map_residue :
    RingHom.ker (MvPolynomial.map (residue R) :
      MvPolynomial ι R →+* MvPolynomial ι (ResidueField R)) = parameterIdeal R ι p := by
  rw [MvPolynomial.ker_map, ker_residue, (Fact.out : Irreducible p).maximalIdeal_eq,
    Ideal.map_span, Set.image_singleton]
  rfl

/-- The quotient equivalence is induced by the original coefficient-reduction map. -/
def quotientResidueEquiv :
    (MvPolynomial ι R ⧸ parameterIdeal R ι p) ≃+* MvPolynomial ι (ResidueField R) :=
  (Ideal.quotEquivOfEq (ker_map_residue R ι p).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (MvPolynomial.map_surjective (residue R) residue_surjective))

@[simp]
theorem quotientResidueEquiv_mk (f : MvPolynomial ι R) :
    quotientResidueEquiv R ι p (Ideal.Quotient.mk _ f) = MvPolynomial.map (residue R) f := by
  simp [quotientResidueEquiv]

/-- The field equivalence extends the actual polynomial quotient equivalence. -/
def residueFieldRingEquiv :
    ResidueField (Ring R ι p) ≃+* FractionRing (MvPolynomial ι (ResidueField R)) :=
  IsFractionRing.ringEquivOfRingEquiv (quotientResidueEquiv R ι p)

@[simp]
theorem residueFieldRingEquiv_polynomial (f : MvPolynomial ι R) :
    residueFieldRingEquiv R ι p
        (residue (Ring R ι p) (algebraMap (MvPolynomial ι R) (Ring R ι p) f)) =
      algebraMap (MvPolynomial ι (ResidueField R))
        (FractionRing (MvPolynomial ι (ResidueField R))) (MvPolynomial.map (residue R) f) := by
  change residueFieldRingEquiv R ι p
    (algebraMap (MvPolynomial ι R ⧸ parameterIdeal R ι p)
      (ResidueField (Ring R ι p)) (Ideal.Quotient.mk _ f)) = _
  rw [residueFieldRingEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    quotientResidueEquiv_mk]

/-- The same equivalence over the canonical original residue-field algebra. -/
def residueFieldAlgEquiv :
    ResidueField (Ring R ι p) ≃ₐ[ResidueField R]
      FractionRing (MvPolynomial ι (ResidueField R)) where
  __ := residueFieldRingEquiv R ι p
  commutes' r := by
    change residueFieldRingEquiv R ι p
      (algebraMap (ResidueField R) (ResidueField (Ring R ι p)) r) = _
    obtain ⟨r, rfl⟩ := residue_surjective r
    rw [ResidueField.algebraMap_residue]
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial ι R) (Ring R ι p)]
    rw [residueFieldRingEquiv_polynomial]
    simp only [MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
    exact (IsScalarTower.algebraMap_apply (ResidueField R)
      (MvPolynomial ι (ResidueField R)) _ (residue R r)).symm

@[simp]
theorem residueFieldAlgEquiv_polynomial (f : MvPolynomial ι R) :
    residueFieldAlgEquiv R ι p
        (residue (Ring R ι p) (algebraMap (MvPolynomial ι R) (Ring R ι p) f)) =
      algebraMap (MvPolynomial ι (ResidueField R))
        (FractionRing (MvPolynomial ι (ResidueField R))) (MvPolynomial.map (residue R) f) :=
  residueFieldRingEquiv_polynomial R ι p f

theorem residueFieldAlgEquiv_X (i : ι) :
    residueFieldAlgEquiv R ι p
        (residue (Ring R ι p) (algebraMap (MvPolynomial ι R) (Ring R ι p) (MvPolynomial.X i))) =
      algebraMap (MvPolynomial ι (ResidueField R))
        (FractionRing (MvPolynomial ι (ResidueField R))) (MvPolynomial.X i) := by
  rw [residueFieldAlgEquiv_polynomial, MvPolynomial.map_X]

theorem residueFieldAlgEquiv_coeff (r : ResidueField R) :
    residueFieldAlgEquiv R ι p (algebraMap (ResidueField R) (ResidueField (Ring R ι p)) r) =
      algebraMap (ResidueField R) (FractionRing (MvPolynomial ι (ResidueField R))) r :=
  (residueFieldAlgEquiv R ι p).commutes r

end ParameterLocalization
