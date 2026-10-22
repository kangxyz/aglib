/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterResidue

/-! # The actual embedding of generic centre residues into the target residue field

The specified embedding of the original centre field extends coefficientwise,
keeping the SAME polynomial variables. Native fraction lifting and the actual
parameter-residue equivalence then give the target map.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace ParameterLocalization

variable (S K ι : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] (p : S) [Fact (Irreducible p)] (e : K →+* ResidueField S)

attribute [local instance] algebraMap_isLocalHom

/-- The polynomial map uses the actual residue embedding and unchanged variables. -/
def genericCentrePolynomialPoint :
    MvPolynomial ι K →+* ResidueField (Ring S ι p) :=
  (residueFieldAlgEquiv S ι p).symm.toRingHom.comp
    ((algebraMap (MvPolynomial ι (ResidueField S))
      (FractionRing (MvPolynomial ι (ResidueField S)))).comp (MvPolynomial.map e))

/-- No nonzero polynomial denominator vanishes at the actual generic target. -/
theorem genericCentrePolynomialPoint_injective :
    Function.Injective (genericCentrePolynomialPoint S K ι p e) :=
  (residueFieldAlgEquiv S ι p).symm.injective.comp
    ((IsFractionRing.injective (MvPolynomial ι (ResidueField S))
      (FractionRing (MvPolynomial ι (ResidueField S)))).comp
      (MvPolynomial.map_injective e e.injective))

/-- The actual generic centre field embeds into the actual generic target residue field. -/
def genericCentreResidueEmbedding :
    FractionRing (MvPolynomial ι K) →+* ResidueField (Ring S ι p) :=
  IsFractionRing.lift (genericCentrePolynomialPoint_injective S K ι p e)

/-- The fraction-field embedding preserves the literal polynomial map. -/
@[simp] theorem genericCentreResidueEmbedding_polynomial (f : MvPolynomial ι K) :
    genericCentreResidueEmbedding S K ι p e
      (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f) =
        (residueFieldAlgEquiv S ι p).symm
          (algebraMap (MvPolynomial ι (ResidueField S))
            (FractionRing (MvPolynomial ι (ResidueField S))) (MvPolynomial.map e f)) :=
  IsFractionRing.lift_algebraMap _ f

/-- Original centre coefficients map through the original specified residue embedding. -/
@[simp] theorem genericCentreResidueEmbedding_coefficient (a : K) :
    genericCentreResidueEmbedding S K ι p e
      (algebraMap K (FractionRing (MvPolynomial ι K)) a) =
        algebraMap (ResidueField S) (ResidueField (Ring S ι p)) (e a) := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial ι K)
    (FractionRing (MvPolynomial ι K)), genericCentreResidueEmbedding_polynomial]
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  simpa only [IsScalarTower.algebraMap_apply (ResidueField S)
    (MvPolynomial ι (ResidueField S)) (FractionRing (MvPolynomial ι (ResidueField S))),
    MvPolynomial.algebraMap_eq] using (residueFieldAlgEquiv S ι p).symm.commutes (e a)

/-- The native residue-field equivalence sends a generic variable back to the
residue of the same actual parameter variable. -/
@[simp] theorem residueFieldAlgEquiv_symm_X (i : ι) :
    (residueFieldAlgEquiv S ι p).symm
      (algebraMap (MvPolynomial ι (ResidueField S))
        (FractionRing (MvPolynomial ι (ResidueField S))) (X i)) =
      residue (Ring S ι p) (algebraMap (MvPolynomial ι S) (Ring S ι p) (X i)) := by
  apply (residueFieldAlgEquiv S ι p).injective
  rw [AlgEquiv.apply_symm_apply, residueFieldAlgEquiv_X]

/-- Generic variables are the residues of the same actual target parameter variables. -/
theorem genericCentreResidueEmbedding_X (i : ι) :
    genericCentreResidueEmbedding S K ι p e
      (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) (X i)) =
        residue (Ring S ι p) (algebraMap (MvPolynomial ι S) (Ring S ι p) (X i)) := by
  rw [genericCentreResidueEmbedding_polynomial, MvPolynomial.map_X,
    residueFieldAlgEquiv_symm_X]

end ParameterLocalization
