/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialNormRoot

/-!
# Actual residue vanishing for principal units

A ring unit reducing to one has zero degree-three residue with two arbitrary
fraction-field entries. At a polynomial place this applies to a quotient of
two equal nonzero residue classes. At infinity it applies to the ratio of two
monic polynomials of the same degree. Other entries may have zeros or poles.
-/

@[expose] public noncomputable section

namespace MilnorK.K3

open MilnorK.K2 Polynomial PolynomialResidue

namespace DVR

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A genuine ring unit reducing to one kills the residue, even when the other
two entries have nonzero valuations. -/
theorem residue_principal_unit (u : Rˣ)
    (hu : Units.map (IsLocalRing.residue R).toMonoidHom u = 1) (a b : Kˣ) :
    residue R K (symbol3 (MilnorK.K2.DVR.fieldUnits R K u) a b) = 0 := by
  let hπ := (IsDiscreteValuationRing.exists_irreducible R).choose_spec
  have hpart : (MilnorK.K2.DVR.data (K := K) hπ).unitPart
      (Additive.ofMul (MilnorK.K2.DVR.fieldUnits R K u)) = 0 := by
    change Additive.ofMul (MilnorK.K2.DVR.unitResidue hπ
      (MilnorK.K2.DVR.fieldUnits R K u)) = 0
    rw [MilnorK.K2.DVR.unitResidue_fieldUnits, hu]
    rfl
  change residue3 (MilnorK.K2.DVR.data hπ) (MilnorK.K2.DVR.unitReductionCompatible hπ) _ = 0
  rw [residue3_symbol, residue3Bilinear_apply, hpart]
  change MilnorK.K2.DVR.value R K (Additive.ofMul (MilnorK.K2.DVR.fieldUnits R K u)) • _ +
    symbolBilinear _ (0 - MilnorK.K2.DVR.value R K
      (Additive.ofMul (MilnorK.K2.DVR.fieldUnits R K u)) • _) _ = 0
  simp only [MilnorK.K2.DVR.value_fieldUnits, zero_smul, sub_zero, map_zero,
    LinearMap.zero_apply, add_zero]

end DVR

namespace PolynomialResidue

variable {k : Type*} [Field k]

/-- Equal nonzero polynomial residues make the first quotient a principal unit;
no restriction is imposed on the other two rational-function entries. -/
theorem residueAt_polynomial_ratio_eq_zero (p f g : k[X]) [Fact (Irreducible p)]
    (hf : f ≠ 0) (hg : g ≠ 0) (hpf : ¬ p ∣ f) (hpg : ¬ p ∣ g)
    (hfg : quotientUnit p f hpf = quotientUnit p g hpg) (a b : (RatFunc k)ˣ) :
    residueAt p (symbol3 (polynomialUnit f hf / polynomialUnit g hg) a b) = 0 := by
  let u := localUnit p f hpf / localUnit p g hpg
  have hu : Units.map (IsLocalRing.residue (Polynomial.LocalResidue.Ring p)).toMonoidHom u = 1 := by
    apply Units.map_injective
      (f := (Polynomial.LocalResidue.residueEquiv p).toRingHom.toMonoidHom)
      (fun x y h => (Polynomial.LocalResidue.residueEquiv p).injective h)
    rw [map_one]
    dsimp only [u]
    rw [_root_.map_div, _root_.map_div, residue_localUnit, residue_localUnit, hfg, div_self']
  rw [residueAt, LinearMap.comp_apply,
    ← fieldUnits_localUnit p f hf hpf, ← fieldUnits_localUnit p g hg hpg, ← _root_.map_div,
    DVR.residue_principal_unit u hu a b, map_zero]

end PolynomialResidue

namespace InfinityResidue

variable {k : Type*} [Field k]

local instance principalUnitVariableIrreducible : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- A ratio of equal-degree monic polynomials has value zero and residue one
at infinity, so its full degree-three residue vanishes. -/
theorem residue_monic_ratio (f g : k[X]) (hf : f.Monic) (hg : g.Monic)
    (hdeg : f.natDegree = g.natDegree) (a b : (RatFunc k)ˣ) :
    residue k (symbol3 (polynomialUnit f hf.ne_zero / polynomialUnit g hg.ne_zero) a b) = 0 := by
  rw [residue, LinearMap.comp_apply, LinearMap.comp_apply, map_symbol3, _root_.map_div,
    inversion_polynomialUnit, inversion_polynomialUnit, hdeg, mul_div_mul_left_eq_div]
  rw [residueAt_polynomial_ratio_eq_zero X f.reverse g.reverse
    (reverse_eq_zero.not.mpr hf.ne_zero) (reverse_eq_zero.not.mpr hg.ne_zero)
    (not_dvd_reverse k f hf.ne_zero) (not_dvd_reverse k g hg.ne_zero)
    ((PolynomialNorm.quotientUnit_reverse_variable f hf).trans
      (PolynomialNorm.quotientUnit_reverse_variable g hg).symm), map_zero]

end InfinityResidue

end MilnorK.K3
