/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.SameUniformizer
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Normalized valuation and literal valuation-ring residues for same-uniformizer maps -/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

universe u v w z
variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  (f : R →+* S) {p : R} (hp : Irreducible p) (hfp : Irreducible (f p))

include hp hfp in
/-- Same-uniformizer maps preserve the normalized integral valuation exactly. -/
theorem intValuation_map_of_map_irreducible (r : R) :
    (maximalIdeal S).intValuation (f r) = (maximalIdeal R).intValuation r := by
  by_cases hr : r = 0
  · simp only [hr, map_zero]
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hr hp
  rw [map_mul, map_pow]
  change (maximalIdeal S).intValuation
      (((Units.map f.toMonoidHom u : Sˣ) : S) * (f p) ^ n) = _
  rw [intValuation_maximalIdeal, intValuation_maximalIdeal,
    addVal_def' (Units.map f.toMonoidHom u) hfp, addVal_def' u hp]

variable (K : Type w) (L : Type z) [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
  (F : K →+* L) (hF : ∀ r : R, F (algebraMap R K r) = algebraMap S L (f r))

include hp hfp hF in
/-- The actual fraction lift is an isometry for the two normalized discrete valuations. -/
theorem valuation_map_of_map_irreducible (x : K) :
    (maximalIdeal S).valuation L (F x) = (maximalIdeal R).valuation K x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  rw [map_div₀, hF, hF, map_div₀, map_div₀,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_map_of_map_irreducible f hp hfp,
    intValuation_map_of_map_irreducible f hp hfp]

/-- The native equivalence has the literal fraction-field inclusion as its underlying map. -/
@[simp] theorem coe_equivValuationSubring (r : R) :
    ((equivValuationSubring (A := R) (K := K) r :
      ((maximalIdeal R).valuation K).valuationSubring) : K) = algebraMap R K r := rfl

/-- Transport of the original map to the literal valuation subrings. -/
def sameUniformizerValuationSubringMap :
    ((maximalIdeal R).valuation K).valuationSubring →+*
      ((maximalIdeal S).valuation L).valuationSubring :=
  (equivValuationSubring (A := S) (K := L)).toRingHom.comp
    (f.comp (equivValuationSubring (A := R) (K := K)).symm.toRingHom)

include hF in
/-- This conjugated map is exactly the restriction of the supplied fraction map. -/
theorem coe_sameUniformizerValuationSubringMap
    (x : ((maximalIdeal R).valuation K).valuationSubring) :
    (sameUniformizerValuationSubringMap f K L x : L) = F (x : K) := by
  obtain ⟨r, rfl⟩ := (equivValuationSubring (A := R) (K := K)).surjective x
  change (equivValuationSubring (A := S) (K := L)
    (f ((equivValuationSubring (A := R) (K := K)).symm
      (equivValuationSubring (A := R) (K := K) r))) : L) =
    F (equivValuationSubring (A := R) (K := K) r : K)
  rw [RingEquiv.symm_apply_apply, coe_equivValuationSubring,
    coe_equivValuationSubring, hF]

include hp hfp in
/-- Locality is inherited from the proved original local map and the native ring equivalences. -/
theorem sameUniformizerValuationSubringMap_isLocalHom :
    IsLocalHom (sameUniformizerValuationSubringMap f K L) := by
  let : IsLocalHom f := isLocalHom_of_map_irreducible f hp hfp
  let eR := equivValuationSubring (A := R) (K := K)
  let eS := equivValuationSubring (A := S) (K := L)
  let : IsLocalHom eR.symm := isLocalHom_equiv eR.symm
  let : IsLocalHom eS := isLocalHom_equiv eS
  let : IsLocalHom eR.symm.toRingHom := isLocalHom_toRingHom eR.symm
  let : IsLocalHom eS.toRingHom := isLocalHom_toRingHom eS
  let : IsLocalHom (f.comp eR.symm.toRingHom) :=
    RingHom.isLocalHom_comp f eR.symm.toRingHom
  exact RingHom.isLocalHom_comp eS.toRingHom (f.comp eR.symm.toRingHom)

/-- The residue identification is induced by the inverse native valuation-ring equivalence. -/
def valuationResidueEquiv (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsLocalRing.ResidueField (((maximalIdeal R).valuation K).valuationSubring) ≃+*
      IsLocalRing.ResidueField R :=
  IsLocalRing.ResidueField.mapEquiv (equivValuationSubring (A := R) (K := K)).symm

@[simp] theorem valuationResidueEquiv_residue (r : R) :
    valuationResidueEquiv R K
        (IsLocalRing.residue (((maximalIdeal R).valuation K).valuationSubring)
          (equivValuationSubring (A := R) (K := K) r)) =
      IsLocalRing.residue R r := by
  change IsLocalRing.residue R
    ((equivValuationSubring (A := R) (K := K)).symm
      (equivValuationSubring (A := R) (K := K) r)) = _
  rw [RingEquiv.symm_apply_apply]

/-- The valuation-subring residue map retains the actual original scalar square. -/
theorem valuationResidueEquiv_map
    (x : IsLocalRing.ResidueField (((maximalIdeal R).valuation K).valuationSubring)) :
    letI : IsLocalHom f := isLocalHom_of_map_irreducible f hp hfp
    letI : IsLocalHom (sameUniformizerValuationSubringMap f K L) :=
      sameUniformizerValuationSubringMap_isLocalHom f hp hfp K L
    valuationResidueEquiv S L
        (IsLocalRing.ResidueField.map (sameUniformizerValuationSubringMap f K L) x) =
      IsLocalRing.ResidueField.map f (valuationResidueEquiv R K x) := by
  let : IsLocalHom f := isLocalHom_of_map_irreducible f hp hfp
  let : IsLocalHom (sameUniformizerValuationSubringMap f K L) :=
    sameUniformizerValuationSubringMap_isLocalHom f hp hfp K L
  change valuationResidueEquiv S L
      (IsLocalRing.ResidueField.map (sameUniformizerValuationSubringMap f K L) x) =
    IsLocalRing.ResidueField.map f (valuationResidueEquiv R K x)
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  change IsLocalRing.residue S
    ((equivValuationSubring (A := S) (K := L)).symm
      (equivValuationSubring (A := S) (K := L)
        (f ((equivValuationSubring (A := R) (K := K)).symm a)))) =
    IsLocalRing.residue S (f ((equivValuationSubring (A := R) (K := K)).symm a))
  rw [RingEquiv.symm_apply_apply]

end IsDiscreteValuationRing
