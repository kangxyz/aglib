/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Symbols
public import Aglib.KTheory.MilnorK.CompatibilityK2
public import Aglib.KTheory.MilnorK.K2.DVR.Basic

/-!
# Specialization in every Milnor degree

The normalized unit-part homomorphism of the existing discrete residue data
induces an actual homomorphism of the standard Milnor quotients in all degrees.
Its Steinberg relation is proved from the positive, zero and negative valuation
cases. The same proof works for the twist `r(a) - v(a) e` by any residue unit.
This twisted specialization is the algebraic input for the sign-correct tame
residue recursion; it does not assert that the unit-part map is a field map.

Actual DVR specializations below use the previously constructed valuation and
literal residue homomorphism. Degree two agrees with the original
`MilnorK2.specialize`; no residue, norm or reciprocity law is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK

universe u v

variable {L : Type u} {κ : Type v} [Field L] [Field κ]

open MilnorK.K2 in
/-- The normalized residue unit part with an arbitrary valuation-linear twist. -/
def unitPartTwist (d : DiscreteResidueData L κ) (e : UnitsAdd κ) :
    UnitsAdd L →ₗ[ℤ] UnitsAdd κ := d.unitPart - d.value.smulRight e

open MilnorK.K2 in
@[simp] theorem unitPartTwist_apply (d : DiscreteResidueData L κ) (e : UnitsAdd κ)
    (a : UnitsAdd L) : unitPartTwist d e a = d.unitPart a - d.value a • e := rfl

open MilnorK.K2 in
/-- Multiplicative form of the twisted residue unit part. -/
def unitPartTwistMul (d : DiscreteResidueData L κ) (e : UnitsAdd κ) : Lˣ →* κˣ :=
  (unitPartTwist d e).toAddMonoidHom.toMultiplicative

open MilnorK.K2 in
@[simp] theorem unitPartTwistMul_apply (d : DiscreteResidueData L κ) (e : UnitsAdd κ)
    (a : Lˣ) : unitPartTwistMul d e a = (d.unitPart (Additive.ofMul a) -
      d.value (Additive.ofMul a) • e).toMul := rfl

open MilnorK.K2 in
/-- Every twist preserves Steinberg, by the elementary valuation/reduction cases. -/
theorem unitPartTwist_steinberg (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (e : UnitsAdd κ) (a b : Lˣ)
    (hab : (a : L) + (b : L) = 1) :
    MilnorK.K2.symbol (unitPartTwistMul d e a) (unitPartTwistMul d e b) = 0 := by
  rcases lt_trichotomy (d.value (Additive.ofMul a)) 0 with hneg | hzero | hpos
  · obtain ⟨hvb, hub⟩ := d.negative a b hab hneg
    have htwist : unitPartTwist d e (Additive.ofMul b) =
        unitPartTwist d e (Additive.ofMul a) + residueSign κ := by
      simp only [unitPartTwist_apply, hvb, hub]
      abel
    change MilnorK.K2.symbol (unitPartTwist d e (Additive.ofMul a)).toMul
      (unitPartTwist d e (Additive.ofMul b)).toMul = 0
    rw [htwist]
    change MilnorK.K2.symbol (unitPartTwist d e (Additive.ofMul a)).toMul
      ((unitPartTwist d e (Additive.ofMul a)).toMul * (-1)) = 0
    simpa using MilnorK.K2.symbol_self_neg (unitPartTwist d e (Additive.ofMul a)).toMul
  · rcases lt_trichotomy (d.value (Additive.ofMul b)) 0 with hbneg | hbzero | hbpos
    · obtain ⟨hva, _⟩ := d.negative b a (by simpa [add_comm] using hab) hbneg
      have hvb : d.value (Additive.ofMul b) = 0 := hva.symm.trans hzero
      simp only [unitPartTwistMul_apply, hzero, hvb, zero_smul, sub_zero]
      exact MilnorK.K2.steinberg _ _ (hd a b hab hzero hvb)
    · simp only [unitPartTwistMul_apply, hzero, hbzero, zero_smul, sub_zero]
      exact MilnorK.K2.steinberg _ _ (hd a b hab hzero hbzero)
    · obtain ⟨_, hua⟩ := d.positive b a (by simpa [add_comm] using hab) hbpos
      simp only [unitPartTwistMul_apply, hzero, hua, zero_smul, sub_zero]
      exact MilnorK.K2.symbol_one_left _
  · obtain ⟨hvb, hub⟩ := d.positive a b hab hpos
    simp only [unitPartTwistMul_apply, hvb, hub, zero_smul, sub_zero]
    exact MilnorK.K2.symbol_one_right _

open MilnorK.K2 in
/-- Twisted specialization descends through every actual all-degree relation. -/
def specializeTwist (d : DiscreteResidueData L κ) (hd : UnitReductionCompatible d)
    (e : UnitsAdd κ) (n : ℕ) : K L n →ₗ[ℤ] K κ n :=
  lift (fun a => symbol (unitPartTwistMul d e ∘ a)) {
    map_mul := by
      intro a i b c
      simp only [Function.comp_update, map_mul]
      exact symbol_mul _ i _ _
    steinberg := by
      intro a i j hij hab
      have h := congrArg (adjacentPairMap (unitPartTwistMul d e ∘ a) i j hij)
        (unitPartTwist_steinberg d hd e (a i) (a j) hab)
      change symbol (Function.update (Function.update (unitPartTwistMul d e ∘ a)
        i ((unitPartTwistMul d e ∘ a) i)) j ((unitPartTwistMul d e ∘ a) j)) = 0 at h
      simpa only [Function.update_eq_self] using h }

open MilnorK.K2 in
@[simp] theorem specializeTwist_symbol (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (e : UnitsAdd κ) (n : ℕ) (a : SymbolTuple L n) :
    specializeTwist d hd e n (symbol a) = symbol (unitPartTwistMul d e ∘ a) :=
  lift_symbol _ _ _

open MilnorK.K2 in
/-- Specialization using the original normalized residue unit parts. -/
def specialize (d : DiscreteResidueData L κ) (hd : UnitReductionCompatible d)
    (n : ℕ) : K L n →ₗ[ℤ] K κ n := specializeTwist d hd 0 n

open MilnorK.K2 in
@[simp] theorem specialize_symbol (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L n) :
    specialize d hd n (symbol a) =
      symbol (fun i => (d.unitPart (Additive.ofMul (a i))).toMul) := by
  simp [specialize, Function.comp_def]

open MilnorK.K2 in
/-- The all-degree construction agrees with the original degree-two specialization. -/
theorem twoEquiv_specialize (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (x : K L 2) :
    twoEquiv κ (specialize d hd 2 x) = MilnorK.K2.specialize d hd (twoEquiv L x) := by
  have h : (twoEquiv κ).toLinearMap.comp (specialize d hd 2) =
      (MilnorK.K2.specialize d hd).comp (twoEquiv L).toLinearMap := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, specialize_symbol,
      twoEquiv_symbol, MilnorK.K2.specialize_symbol]
  exact LinearMap.congr_fun h x

open MilnorK.K2 in
/-- The original uniformizer has zero specialization in any positive-degree symbol. -/
theorem specialize_symbol_uniformizer (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L n)
    (i : Fin n) (hi : a i = d.uniformizer) : specialize d hd n (symbol a) = 0 := by
  rw [specialize_symbol]
  apply symbol_eq_zero_of_eq_one _ i
  simp [hi, d.unitPart_uniformizer]

namespace DVR

variable (R L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- All-degree specialization from an actual DVR and a specified uniformizer. -/
def specializeWithUniformizer {π : R} (hπ : Irreducible π) (n : ℕ) :
    K L n →ₗ[ℤ] K (IsLocalRing.ResidueField R) n :=
  MilnorK.specialize (MilnorK.K2.DVR.data (K := L) hπ)
    (MilnorK.K2.DVR.unitReductionCompatible hπ) n

/-- A chosen actual uniformizer gives specialization in every degree. -/
def specialize (n : ℕ) : K L n →ₗ[ℤ] K (IsLocalRing.ResidueField R) n :=
  specializeWithUniformizer R L (IsDiscreteValuationRing.exists_irreducible R).choose_spec n

/-- On ring-unit symbols this is literal coordinatewise reduction. -/
theorem specializeWithUniformizer_ring_units {π : R} (hπ : Irreducible π)
    (n : ℕ) (a : Fin n → Rˣ) :
    specializeWithUniformizer R L hπ n
      (symbol (MilnorK.K2.DVR.fieldUnits R L ∘ a)) =
      symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) := by
  rw [specializeWithUniformizer, MilnorK.specialize_symbol]
  congr 1
  funext i
  exact MilnorK.K2.DVR.unitResidue_fieldUnits hπ (a i)

/-- The chosen specialization has the same literal ring-unit reduction formula. -/
theorem specialize_ring_units (n : ℕ) (a : Fin n → Rˣ) :
    specialize R L n (symbol (MilnorK.K2.DVR.fieldUnits R L ∘ a)) =
      symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) :=
  specializeWithUniformizer_ring_units R L _ n a

end DVR

end MilnorK
