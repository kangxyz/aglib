/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.DVR.Uniformizer

/-!
# Actual ramified restriction in Milnor K₂

For a local homomorphism of actual DVRs and a commuting map of fraction fields,
a literal equality `j(πR) = u * πS^e` determines integer-order scaling and the
change in normalized unit residues. These are derived from the original DVR
normalization, rather than imposed as compatibility hypotheses.

The existing tame map satisfies `tL(res x) = e • res(tR x)`. The existing
specialization uses normalization by `π`, and satisfies
`sL(res x) = res(sR x) + {res(tR x), ū}`. The sign is derived using the existing
Milnor symbol identities; no new specialization or minus-uniformizer convention
is substituted. The resulting joint-kernel annihilation needs no residue norm,
finite-degree assumption, or higher-degree K-theory.
-/

@[expose] public noncomputable section

namespace MilnorK.K2.DVR

open IsLocalRing

private theorem ramified_unitsLinear_sign {k l : Type*} [Field k] [Field l]
    (f : k →+* l) : unitsLinear f (residueSign k) = residueSign l := by
  change Additive.ofMul (Units.map f.toMonoidHom (-1)) = Additive.ofMul (-1)
  congr 1
  apply Units.ext
  change f (-1) = -1
  simp

private theorem ramified_map_symbolBilinear {k l : Type*} [Field k] [Field l]
    (f : k →+* l) (a b : UnitsAdd k) :
    map f (symbolBilinear k a b) =
      symbolBilinear l (unitsLinear f a) (unitsLinear f b) := rfl

private theorem ramified_tame_algebra {k : Type*} [Field k]
    (a b c : UnitsAdd k) (m n e : ℤ) :
    ((e * m) * (e * n)) • residueSign k +
        (e * n) • (a + m • c) - (e * m) • (b + n • c) =
      e • ((m * n) • residueSign k + n • a - m • b) := by
  have hs : (e * e) • residueSign k = e • residueSign k := by
    apply sub_eq_zero.mp
    rw [← sub_smul]
    exact square_sub_smul_eq_zero _ residueSign_add_self e
  have hsign : ((e * m) * (e * n)) • residueSign k =
      (e * (m * n)) • residueSign k := by
    calc
      _ = (m * n) • ((e * e) • residueSign k) := by
        rw [smul_smul]
        congr 1
        ring
      _ = _ := by
        rw [hs, smul_smul]
        congr 1
        ring
  simp only [zsmul_add, zsmul_sub, ← mul_zsmul]
  rw [hsign]
  have hc : (e * n) * m = (e * m) * n := by ring
  rw [hc]
  abel

/-- A local ring map cannot send an irreducible source uniformizer to a unit. -/
theorem ramificationIndex_pos {R S : Type*} [CommRing R] [CommRing S]
    (j : R →+* S) [IsLocalHom j] {πR : R} {πS : S}
    (hπR : Irreducible πR) (u : Sˣ) (e : ℕ)
    (hπ : j πR = (u : S) * πS ^ e) : 0 < e := by
  apply Nat.pos_of_ne_zero
  intro he
  have hu : IsUnit (j πR) := by
    rw [hπ, he, pow_zero, mul_one]
    exact u.isUnit
  exact hπR.not_isUnit (isUnit_of_map_unit j πR hu)

/-- Restriction on multiplicative units is injective for an actual field homomorphism. -/
theorem residueUnitsLinear_injective {k l : Type*} [Field k] [Field l]
    (f : k →+* l) : Function.Injective (unitsLinear f) := by
  intro a b h
  apply Additive.ext
  apply Units.ext
  apply f.injective
  exact congrArg (fun z : UnitsAdd l => (z.toMul : l)) h

variable {R S K L : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- Reconstructing a fraction-field unit from its actual normalized ring-unit lift. -/
theorem normalizedLift_decomposition {π : R} (hπ : Irreducible π) (a : Kˣ) :
    a = fieldUnits R K (normalizedLift (K := K) hπ a) *
      uniformizer (K := K) hπ ^ value R K (Additive.ofMul a) := by
  rw [normalizedLift_spec]
  simp [normalizedUnit, mul_assoc]

variable (j : R →+* S) (F : K →+* L)
  (hF : ∀ r : R, F (algebraMap R K r) = algebraMap S L (j r))

include hF

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S]
  [IsDiscreteValuationRing S] [IsFractionRing R K] [IsFractionRing S L] in
/-- The commuting fraction-field square also commutes on genuine ring units. -/
theorem ramified_fieldUnits_map (a : Rˣ) :
    Units.map F.toMonoidHom (fieldUnits R K a) =
      fieldUnits S L (Units.map j.toMonoidHom a) := by
  apply Units.ext
  exact hF (a : R)

variable {πR : R} {πS : S} (hπR : Irreducible πR) (hπS : Irreducible πS)
  (u : Sˣ) (e : ℕ) (hπ : j πR = (u : S) * πS ^ e)

include hπR hπS hπ

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S]
  [IsDiscreteValuationRing S] in
/-- The literal uniformizer equality transports to the original fraction-field units. -/
theorem ramified_uniformizer_map :
    Units.map F.toMonoidHom (uniformizer (K := K) hπR) =
      fieldUnits S L u * uniformizer (K := L) hπS ^ e := by
  apply Units.ext
  change F (algebraMap R K πR) =
    algebraMap S L (u : S) * algebraMap S L πS ^ e
  rw [hF, hπ, map_mul, map_pow]

omit [IsDomain S] [IsDiscreteValuationRing S] in
/-- Transporting the normalized-lift decomposition gives the target unit factors. -/
theorem ramified_decomposition (a : Kˣ) :
    Units.map F.toMonoidHom a =
      fieldUnits S L (Units.map j.toMonoidHom (normalizedLift (K := K) hπR a)) *
        fieldUnits S L u ^ value R K (Additive.ofMul a) *
          uniformizer (K := L) hπS ^ ((e : ℤ) * value R K (Additive.ofMul a)) := by
  conv_lhs => rw [normalizedLift_decomposition hπR a]
  rw [map_mul, map_zpow, ramified_fieldUnits_map j F hF,
    ramified_uniformizer_map j F hF hπR hπS u e hπ, mul_zpow]
  rw [← zpow_natCast, ← zpow_mul]
  ac_rfl

/-- Integer-order scaling follows from the actual target ring-unit decomposition. -/
theorem ramified_value_map (a : UnitsAdd K) :
    value S L (unitsLinear F a) = (e : ℤ) * value R K a := by
  have h := congrArg (fun b : Lˣ => value S L (Additive.ofMul b))
    (ramified_decomposition j F hF hπR hπS u e hπ a.toMul)
  simp only [ofMul_mul, ofMul_zpow, map_add, map_smul, value_fieldUnits,
    value_uniformizer, smul_eq_mul, mul_zero, zero_add, mul_one] at h
  exact h

/-- The normalized target lift is the mapped source lift times the ramification unit. -/
theorem ramified_normalizedLift_map (a : Kˣ) :
    normalizedLift (K := L) hπS (Units.map F.toMonoidHom a) =
      Units.map j.toMonoidHom (normalizedLift (K := K) hπR a) *
        u ^ value R K (Additive.ofMul a) := by
  apply fieldUnits_injective S L
  rw [normalizedLift_spec, map_mul, map_zpow]
  change Units.map F.toMonoidHom a * uniformizer (K := L) hπS ^
    (-value S L (unitsLinear F (Additive.ofMul a))) = _
  rw [ramified_value_map j F hF hπR hπS u e hπ,
    ramified_decomposition j F hF hπR hπS u e hπ a]
  simp [mul_assoc]

variable [IsLocalHom j]

/-- Literal reduction of the ramification unit in the actual target residue field. -/
def ramificationUnitResidue (u : Sˣ) : UnitsAdd (ResidueField S) :=
  Additive.ofMul (Units.map (residue S).toMonoidHom u)

/-- Angular components transform by the reduction of `u` raised to the source order. -/
theorem ramified_unitResidue_map (a : Kˣ) :
    unitResidue (K := L) hπS (Units.map F.toMonoidHom a) =
      Units.map (ResidueField.map j).toMonoidHom (unitResidue (K := K) hπR a) *
        Units.map (residue S).toMonoidHom u ^ value R K (Additive.ofMul a) := by
  change Units.map (residue S).toMonoidHom
    (normalizedLift (K := L) hπS (Units.map F.toMonoidHom a)) = _
  rw [ramified_normalizedLift_map j F hF hπR hπS u e hπ, map_mul, map_zpow]
  congr 1

/-- Additive angular-component transformation, derived from the actual DVR data. -/
theorem ramified_unitPart_map (a : UnitsAdd K) :
    unitPart (K := L) hπS (unitsLinear F a) =
      unitsLinear (ResidueField.map j) (unitPart (K := K) hπR a) +
        value R K a • ramificationUnitResidue u := by
  exact congrArg Additive.ofMul
    (ramified_unitResidue_map j F hF hπR hπS u e hπ a.toMul)

/-- Ramified restriction of the original signed tame map on every Milnor class. -/
theorem ramified_tame_restrict :
    (tame (data (K := L) hπS)).comp (map F) =
      (e : ℤ) • ((unitsLinear (ResidueField.map j)).comp (tame (data (K := K) hπR))) := by
  apply linearMap_ext
  intro a b
  change rawTame (data hπS) (unitsLinear F (Additive.ofMul a))
      (unitsLinear F (Additive.ofMul b)) =
    (e : ℤ) • unitsLinear (ResidueField.map j)
      (rawTame (data hπR) (Additive.ofMul a) (Additive.ofMul b))
  simp only [rawTame, data, ramified_value_map j F hF hπR hπS u e hπ,
    ramified_unitPart_map j F hF hπR hπS u e hπ, map_add, map_sub, map_smul,
    ramified_unitsLinear_sign]
  exact ramified_tame_algebra _ _ _ _ _ _

/-- The exact correction for the original normalization by `π` has a plus sign. -/
theorem ramified_specialize_restrict :
    (specialize (data (K := L) hπS) (unitReductionCompatible hπS)).comp (map F) =
      (map (ResidueField.map j)).comp
          (specialize (data (K := K) hπR) (unitReductionCompatible hπR)) +
        (residueCorrection (ramificationUnitResidue u)).comp
          ((unitsLinear (ResidueField.map j)).comp (tame (data (K := K) hπR))) := by
  apply linearMap_ext
  intro a b
  change symbolBilinear (ResidueField S)
      (unitPart (K := L) hπS (unitsLinear F (Additive.ofMul a)))
      (unitPart (K := L) hπS (unitsLinear F (Additive.ofMul b))) =
    map (ResidueField.map j) (symbolBilinear (ResidueField R)
      (unitPart (K := K) hπR (Additive.ofMul a))
      (unitPart (K := K) hπR (Additive.ofMul b))) +
    symbolBilinear (ResidueField S)
      (unitsLinear (ResidueField.map j)
        (rawTame (data hπR) (Additive.ofMul a) (Additive.ofMul b)))
      (ramificationUnitResidue u)
  simp only [ramified_unitPart_map j F hF hπR hπS u e hπ,
    ramified_map_symbolBilinear, rawTame, data, map_add, map_sub, map_smul,
    ramified_unitsLinear_sign]
  simpa only [zsmul_neg, sub_neg_eq_add, map_neg, map_add, map_sub, map_smul] using
    (bilinear_symbol_change
      (unitsLinear (ResidueField.map j) (unitPart (K := K) hπR (Additive.ofMul a)))
      (unitsLinear (ResidueField.map j) (unitPart (K := K) hπR (Additive.ofMul b)))
      (-ramificationUnitResidue u) (value R K (Additive.ofMul a))
      (value R K (Additive.ofMul b)))

/-- Vanishing of the upstairs tame defect annihilates the original downstairs tame value. -/
theorem ramified_tame_annihilated (x : Group K)
    (hx : tame (data (K := L) hπS) (map F x) = 0) :
    (e : ℤ) • tame (data (K := K) hπR) x = 0 := by
  apply residueUnitsLinear_injective (ResidueField.map j)
  rw [map_smul, map_zero]
  have h := LinearMap.congr_fun (ramified_tame_restrict j F hF hπR hπS u e hπ) x
  exact h.symm.trans hx

/-- Both original upstairs defects vanishing forces the two downstairs annihilation claims.
The specialization conclusion is in the actual target residue field; no injectivity on K₂
or residue-field norm is silently assumed. -/
theorem ramified_joint_kernel_annihilation (x : Group K)
    (ht : tame (data (K := L) hπS) (map F x) = 0)
    (hs : specialize (data (K := L) hπS) (unitReductionCompatible hπS) (map F x) = 0) :
    (e : ℤ) • tame (data (K := K) hπR) x = 0 ∧
      (e : ℤ) • map (ResidueField.map j)
        (specialize (data (K := K) hπR) (unitReductionCompatible hπR) x) = 0 := by
  have ht0 := ramified_tame_annihilated j F hF hπR hπS u e hπ x ht
  refine ⟨ht0, ?_⟩
  have hcorr : (e : ℤ) • residueCorrection (ramificationUnitResidue u)
      (unitsLinear (ResidueField.map j) (tame (data (K := K) hπR) x)) = 0 := by
    rw [← map_smul, ← map_smul, ht0, map_zero, map_zero]
  have h := LinearMap.congr_fun (ramified_specialize_restrict j F hF hπR hπS u e hπ) x
  change specialize (data hπS) (unitReductionCompatible hπS) (map F x) =
    map (ResidueField.map j) (specialize (data hπR) (unitReductionCompatible hπR) x) +
      residueCorrection (ramificationUnitResidue u)
        (unitsLinear (ResidueField.map j) (tame (data hπR) x)) at h
  have he := congrArg (fun z : Group (ResidueField S) => (e : ℤ) • z) h
  rw [hs, smul_zero, smul_add, hcorr, add_zero] at he
  exact he.symm

end MilnorK.K2.DVR
