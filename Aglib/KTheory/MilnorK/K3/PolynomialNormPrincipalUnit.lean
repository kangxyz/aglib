/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialNormSplit
public import Aglib.KTheory.MilnorK.K3.PolynomialNormRestrictionKernel
public import Aglib.KTheory.MilnorK.K2.DVR.RamifiedRestriction
public import Aglib.RingTheory.HenselianPrincipalRoots
public import Aglib.RingTheory.CompleteDVRExtension
public import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Principal-unit polynomial norms over complete DVRs

The theorem below concerns the original polynomial norm and original tame and
specialization maps. Its inputs are actual DVRs, actual local branch maps,
literal commuting fraction-field squares, a finite residue extension with its
literal scalar map, and a literal uniformizer ramification equality. It assumes
no norm compatibility, restriction injectivity on K₂, or vanishing conclusion.

Splitting annihilates both upstairs defects. Ramified restriction and the finite
residue degree give one fixed annihilator. Hensel divisibility in the same source
DVR removes it. The final complete-DVR theorem constructs all these local data
from the actual integral closures in the source and its chosen splitting field.
The normalization/completion descent for noncomplete coefficient DVRs remains
separate, as do general norm/tame compatibility and a U¹-kernel identification.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing
open MilnorK.K2 MilnorK.K2.DVR

section PrincipalSymbols

variable {S L : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]
  {πS : S} (hπS : Irreducible πS)

/-- A genuine principal ring unit has zero additive angular component. -/
theorem unitPart_principal (h : Sˣ) (hh : residue S (h : S) = 1) :
    unitPart (K := L) hπS (Additive.ofMul (fieldUnits S L h)) = 0 := by
  change Additive.ofMul (unitResidue hπS (fieldUnits S L h)) = 0
  rw [unitResidue_fieldUnits, show Units.map (residue S).toMonoidHom h = 1 from
    Units.ext hh]
  rfl

/-- Both actual defects vanish when the second entry is a principal ring unit;
the first entry is an arbitrary fraction-field unit. -/
theorem joint_vanish_principal_symbol (b : Lˣ) (h : Sˣ)
    (hh : residue S (h : S) = 1) :
    tame (data (K := L) hπS) (symbol b (fieldUnits S L h)) = 0 ∧
      specialize (data (K := L) hπS) (unitReductionCompatible hπS)
        (symbol b (fieldUnits S L h)) = 0 := by
  have hu := unitPart_principal (L := L) hπS h hh
  constructor
  · simp only [tame_symbol, rawTame, data, value_fieldUnits, hu,
      mul_zero, zero_smul, smul_zero, add_zero, sub_zero]
  · rw [specialize_symbol]
    change symbol _ (unitPart (K := L) hπS (Additive.ofMul (fieldUnits S L h))).toMul = 0
    rw [hu]
    exact symbol_one_right _

end PrincipalSymbols

section BoundedKernel

variable {R S K L : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]
  (j : R →+* S) [IsLocalHom j] (F : K →+* L)
  (hF : ∀ r : R, F (algebraMap R K r) = algebraMap S L (j r))
  {πR : R} {πS : S} (hπR : Irreducible πR) (hπS : Irreducible πS)
  (u : Sˣ) (e : ℕ) (hπ : j πR = (u : S) * πS ^ e)
  [Algebra (ResidueField R) (ResidueField S)]
  [FiniteDimensional (ResidueField R) (ResidueField S)]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
  (hκ : algebraMap (ResidueField R) (ResidueField S) = ResidueField.map j)

include hF hπ hκ

/-- The actual ramification index times the actual finite residue degree kills
both downstairs defects of any class whose two restricted defects vanish. -/
theorem jointKernel_restrict_annihilator (x : MilnorK.K2.Group K)
    (ht : tame (data (K := L) hπS) (MilnorK.K2.map F x) = 0)
    (hs : specialize (data (K := L) hπS) (unitReductionCompatible hπS)
      (MilnorK.K2.map F x) = 0) :
    ((e * Module.finrank (ResidueField R) (ResidueField S) : ℕ) : ℤ) •
        tame (data (K := K) hπR) x = 0 ∧
      ((e * Module.finrank (ResidueField R) (ResidueField S) : ℕ) : ℤ) •
        specialize (data (K := K) hπR) (unitReductionCompatible hπR) x = 0 := by
  obtain ⟨ht0, hs0⟩ := ramified_joint_kernel_annihilation j F hF hπR hπS u e hπ x ht hs
  constructor
  · rw [Nat.cast_mul, mul_comm, mul_smul, ht0, smul_zero]
  · rw [← hκ] at hs0
    simpa only [Nat.cast_mul] using
      mul_finrank_smul_eq_zero_of_smul_map_eq_zero
        (ResidueField R) (ResidueField S) (e : ℤ) _ hs0

end BoundedKernel

section SplitPrincipal

variable {B S K L : Type*}
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [CharZero K] [Field L]
  [Algebra S L] [IsFractionRing S L]
  (F : K →+* L) (p : MonicIrreducible K) (hp : (p.val.map F).Splits)
  [Algebra B (AdjoinRoot p.val)] [IsFractionRing B (AdjoinRoot p.val)]
  (β : ∀ _q : {q // q ∈ placesAbove F p}, B →+* S)
  [∀ _q, IsLocalHom (β _q)]
  (hβ : ∀ (q : {q // q ∈ placesAbove F p}) (r : B),
    splitBranchMap F p hp q (algebraMap B (AdjoinRoot p.val) r) =
      algebraMap S L (β q r))
  {πS : S} (hπS : Irreducible πS)

include hβ

omit [CharZero K] [IsFractionRing S L] [IsFractionRing B (AdjoinRoot p.val)] in
/-- Every actual split branch carries a principal source unit to a principal
unit by its local ring map and literal fraction compatibility. -/
theorem splitBranch_principal (q : {q // q ∈ placesAbove F p})
    (h : Bˣ) (hh : residue B (h : B) = 1) :
    Units.map (splitBranchMap F p hp q).toMonoidHom
        (fieldUnits B (AdjoinRoot p.val) h) =
      fieldUnits S L (Units.map (β q).toMonoidHom h) ∧
      residue S (Units.map (β q).toMonoidHom h : S) = 1 := by
  constructor
  · exact ramified_fieldUnits_map (β q) (splitBranchMap F p hp q) (hβ q) h
  · change residue S (β q (h : B)) = 1
    rw [← ResidueField.map_residue, hh, map_one]

omit [IsFractionRing B (AdjoinRoot p.val)] in
open scoped Classical in
/-- The full exact split norm sum has both defects zero upstairs. No hypothesis
on the arbitrary first coordinate or on its valuation is used. -/
theorem split_norm_joint_vanish (b : (AdjoinRoot p.val)ˣ) (h : Bˣ)
    (hh : residue B (h : B) = 1) :
    tame (data (K := L) hπS)
        (MilnorK.K2.map F (polynomialNorm p (symbol b (fieldUnits B (AdjoinRoot p.val) h)))) = 0 ∧
      specialize (data (K := L) hπS) (unitReductionCompatible hπS)
        (MilnorK.K2.map F
          (polynomialNorm p (symbol b (fieldUnits B (AdjoinRoot p.val) h)))) = 0 := by
  rw [polynomialNorm_restrict_symbol_of_splits F p hp]
  have hv : ∀ q : {q // q ∈ placesAbove F p},
      tame (data (K := L) hπS)
        (symbol (Units.map (splitBranchMap F p hp q).toMonoidHom b)
          (Units.map (splitBranchMap F p hp q).toMonoidHom
            (fieldUnits B (AdjoinRoot p.val) h))) = 0 ∧
      specialize (data (K := L) hπS) (unitReductionCompatible hπS)
        (symbol (Units.map (splitBranchMap F p hp q).toMonoidHom b)
          (Units.map (splitBranchMap F p hp q).toMonoidHom
            (fieldUnits B (AdjoinRoot p.val) h))) = 0 := by
    intro q
    obtain ⟨hq, hr⟩ := splitBranch_principal F p hp β hβ q h hh
    rw [hq]
    exact joint_vanish_principal_symbol hπS _ _ hr
  constructor
  · rw [map_sum]
    exact Finset.sum_eq_zero fun q _ => (hv q).1
  · rw [map_sum]
    exact Finset.sum_eq_zero fun q _ => (hv q).2

end SplitPrincipal

section PrincipalNorm

variable {R B S K L : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [HenselianLocalRing B]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]
  [CharZero (ResidueField B)]
  (j : R →+* S) [IsLocalHom j] (F : K →+* L)
  (hF : ∀ r : R, F (algebraMap R K r) = algebraMap S L (j r))
  (p : MonicIrreducible K) (hp : (p.val.map F).Splits)
  [Algebra B (AdjoinRoot p.val)] [IsFractionRing B (AdjoinRoot p.val)]
  (β : ∀ _q : {q // q ∈ placesAbove F p}, B →+* S)
  [∀ _q, IsLocalHom (β _q)]
  (hβ : ∀ (q : {q // q ∈ placesAbove F p}) (r : B),
    splitBranchMap F p hp q (algebraMap B (AdjoinRoot p.val) r) =
      algebraMap S L (β q r))
  {πR : R} {πS : S} (hπR : Irreducible πR) (hπS : Irreducible πS)
  (u : Sˣ) (e : ℕ) (hπ : j πR = (u : S) * πS ^ e)
  [Algebra (ResidueField R) (ResidueField S)]
  [FiniteDimensional (ResidueField R) (ResidueField S)]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
  (hκ : algebraMap (ResidueField R) (ResidueField S) = ResidueField.map j)

include hF hβ hπ hκ hπS

omit [IsFractionRing B (AdjoinRoot p.val)] in
/-- Concrete-DVR principal-unit polynomial norm vanishing. The root used to
remove the fixed `e*f` annihilator lies in the same henselian DVR `B`; neither
the polynomial presentation nor the splitting field is changed. -/
theorem polynomialNorm_principal_unit_joint_vanish
    (b : (AdjoinRoot p.val)ˣ) (h : Bˣ) (hh : residue B (h : B) = 1) :
    tame (data (K := K) hπR)
        (polynomialNorm p (symbol b (fieldUnits B (AdjoinRoot p.val) h))) = 0 ∧
      specialize (data (K := K) hπR) (unitReductionCompatible hπR)
        (polynomialNorm p (symbol b (fieldUnits B (AdjoinRoot p.val) h))) = 0 := by
  let D : ℕ := e * Module.finrank (ResidueField R) (ResidueField S)
  have hD : 0 < D := Nat.mul_pos (ramificationIndex_pos j hπR u e hπ)
    (Module.finrank_pos (R := ResidueField R) (M := ResidueField S))
  obtain ⟨h', hh', hpow⟩ :=
    HenselianLocalRing.PrincipalRoots.exists_pow_eq_of_residue_charZero D hD h hh
  obtain ⟨ht, hs⟩ := split_norm_joint_vanish F p hp β hβ hπS b h' hh'
  obtain ⟨ht0, hs0⟩ := jointKernel_restrict_annihilator j F hF hπR hπS u e hπ hκ
    (polynomialNorm p (symbol b (fieldUnits B (AdjoinRoot p.val) h'))) ht hs
  have hz : polynomialNorm p (symbol b (fieldUnits B (AdjoinRoot p.val) h)) =
      (D : ℤ) • polynomialNorm p (symbol b (fieldUnits B (AdjoinRoot p.val) h')) := by
    rw [← hpow, map_pow, symbol_pow_right, map_nsmul, natCast_zsmul]
  constructor
  · rw [hz, map_smul]
    exact ht0
  · rw [hz, map_smul]
    exact hs0

end PrincipalNorm

section CompleteDVR

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CharZero (ResidueField R)]

/-- Principal-unit polynomial norms over a complete DVR. The source DVR is the
actual integral closure of `R` in the original `AdjoinRoot p`. The splitting
field, its integral-closure DVR, all local branch maps, finite residue degree,
and positive ramification are constructed in the proof. Both field algebras
are the canonical scalar extensions, so no compatibility input is supplied. -/
theorem polynomialNorm_principal_unit_completeDVR
    (p : MonicIrreducible K)
    {πR : R} (hπR : Irreducible πR)
    (b : (AdjoinRoot p.val)ˣ) (h : (integralClosure R (AdjoinRoot p.val))ˣ) :
    let _ : CharZero R := RingHom.charZero (residue R)
    let _ : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
    let _ := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
    let _ := IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing
      R K (AdjoinRoot p.val)
    residue (integralClosure R (AdjoinRoot p.val)) (h : integralClosure R (AdjoinRoot p.val)) = 1 →
      tame (data (K := K) hπR)
          (polynomialNorm p (symbol b (fieldUnits (integralClosure R (AdjoinRoot p.val))
            (AdjoinRoot p.val) h))) = 0 ∧
        specialize (data (K := K) hπR) (unitReductionCompatible hπR)
          (polynomialNorm p (symbol b (fieldUnits (integralClosure R (AdjoinRoot p.val))
            (AdjoinRoot p.val) h))) = 0 := by
  let : CharZero R := RingHom.charZero (residue R)
  let : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  let : FiniteDimensional K (AdjoinRoot p.val) :=
    (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
  let B := integralClosure R (AdjoinRoot p.val)
  let : IsDiscreteValuationRing B :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing
      R K (AdjoinRoot p.val)
  dsimp only
  intro hh
  let : IsLocalHom (algebraMap R B) :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_isLocalHom R K (AdjoinRoot p.val)
  let : CharZero (ResidueField B) :=
    charZero_of_injective_algebraMap (algebraMap (ResidueField R) (ResidueField B)).injective
  let : HenselianLocalRing B :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_henselianLocalRing
      R K (AdjoinRoot p.val)
  let L := p.val.SplittingField
  let S := integralClosure R L
  let : IsDiscreteValuationRing S :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing R K L
  let : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  let : IsLocalHom (algebraMap R S) :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_isLocalHom R K L
  let : FiniteDimensional (ResidueField R) (ResidueField S) :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_residue_finite R K L
  let hp : (p.val.map (algebraMap K L)).Splits := Polynomial.SplittingField.splits p.val
  let σ (q : {q // q ∈ placesAbove (algebraMap K L) p}) : AdjoinRoot p.val →ₐ[K] L :=
    { splitBranchMap (algebraMap K L) p hp q with
      commutes' := splitBranchMap_algebraMap (algebraMap K L) p hp q }
  let β (q : {q // q ∈ placesAbove (algebraMap K L) p}) : B →+* S :=
    ((σ q).restrictScalars R).mapIntegralClosure.toRingHom
  let : ∀ q, IsLocalHom (β q) := fun q =>
    IsDiscreteValuationRing.CompleteExtension.mapIntegralClosure_isLocalHom
      ((σ q).restrictScalars R)
  have hβ (q : {q // q ∈ placesAbove (algebraMap K L) p}) (r : B) :
      splitBranchMap (algebraMap K L) p hp q (algebraMap B (AdjoinRoot p.val) r) =
        algebraMap S L (β q r) := rfl
  obtain ⟨πS, hπS⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨e, _, u, hπ⟩ :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_exists_positive_ramification
      R K L hπR hπS
  have hκ : algebraMap (ResidueField R) (ResidueField S) =
      ResidueField.map (algebraMap R S) := by
    ext x
    obtain ⟨r, rfl⟩ := residue_surjective x
    rfl
  exact polynomialNorm_principal_unit_joint_vanish (algebraMap R S) (algebraMap K L)
    (fun r => (IsScalarTower.algebraMap_apply R K L r).symm.trans
      (IsScalarTower.algebraMap_apply R S L r))
    p hp β hβ hπR hπS u e hπ hκ b h hh

end CompleteDVR

end MilnorK.K3.PolynomialNorm
