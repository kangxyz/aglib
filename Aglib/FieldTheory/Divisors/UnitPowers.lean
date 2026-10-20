/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.FieldTheory.Divisors.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Powers of units and a supplied divisor kernel

Source: `R5Lab.Aglib.FieldTheory.Divisors.UnitPowers`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

namespace Field.DivisorData

variable {C K Div : Type*} [Field C] [Field K] [AddCommGroup Div]
  [IsAddTorsionFree Div] (d : DivisorData C K Div)

/-- If a positive power of a function equals a constant, that function is a
constant and its constant preimage has the specified power. -/
theorem exists_constant_of_pow_eq_constant {n : ℕ} (hn : 0 < n)
    (a : Cˣ) (g : Kˣ) (hg : g ^ n = d.constant a) :
    ∃ b : Cˣ, g = d.constant b ∧ b ^ n = a := by
  have hz : n • d.divisor (Additive.ofMul g) = 0 := by
    rw [← d.divisor_pow, hg, d.divisor_constant]
  have hgzero : d.divisor (Additive.ofMul g) = 0 := by
    exact (nsmul_eq_zero_iff_right hn.ne').mp hz
  obtain ⟨b, hb⟩ := (d.kernel_eq_constants g).mp hgzero
  change d.constant b = g at hb
  refine ⟨b, hb.symm, ?_⟩
  apply d.constant_injective
  rw [d.constant_pow, hb, hg]

/-- A constant has a positive-degree root in the function field exactly when
it has a root of that degree in the constant field. -/
theorem constant_is_pow_iff {n : ℕ} (hn : 0 < n) (a : Cˣ) :
    (∃ g : Kˣ, g ^ n = d.constant a) ↔ ∃ b : Cˣ, b ^ n = a := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨b, _, hb⟩ := d.exists_constant_of_pow_eq_constant hn a g hg
    exact ⟨b, hb⟩
  · rintro ⟨b, rfl⟩
    exact ⟨d.constant b, (d.constant_pow b n).symm⟩

end Field.DivisorData
namespace Field
/-- The subgroup of actual `n`th powers of units. -/
def unitPowers (F : Type*) [Field F] (n : ℕ) : Subgroup Fˣ :=
  (powMonoidHom n : Fˣ →* Fˣ).range

/-- Unit classes modulo actual `n`th powers; the target symbol remains integral. -/
abbrev UnitPowerQuotient (F : Type*) [Field F] (n : ℕ) := Fˣ ⧸ unitPowers F n

namespace DivisorData

variable {C K Div : Type*} [Field C] [Field K] [AddCommGroup Div]
  (d : DivisorData C K Div)

/-- The actual constant inclusion descends to quotients by unit powers. This
construction itself does not require a torsion-free divisor group. -/
def constantPowerQuotientMap (n : ℕ) : UnitPowerQuotient C n →* UnitPowerQuotient K n :=
  QuotientGroup.map (unitPowers C n) (unitPowers K n) (Units.map d.constants.toMonoidHom) (by
    intro a ha
    obtain ⟨b, hb⟩ := ha
    change b ^ n = a at hb
    refine ⟨d.constant b, ?_⟩
    change d.constant b ^ n = d.constant a
    rw [← d.constant_pow, hb])

/-- A constant quotient representative maps to the same embedded constant. -/
@[simp] theorem constantPowerQuotientMap_mk (n : ℕ) (a : Cˣ) :
    d.constantPowerQuotientMap n (QuotientGroup.mk a) =
      QuotientGroup.mk (d.constant a) := rfl

variable [IsAddTorsionFree Div]

/-- Pulling positive powers back along the constant inclusion gives exactly
the constant-field power subgroup. -/
theorem unitPowers_comap_constant {n : ℕ} (hn : 0 < n) :
    (unitPowers K n).comap (Units.map d.constants.toMonoidHom) = unitPowers C n := by
  ext a
  change (∃ g : Kˣ, g ^ n = d.constant a) ↔ ∃ b : Cˣ, b ^ n = a
  exact d.constant_is_pow_iff hn a

/-- Constant unit classes inject into function-field unit classes modulo a
positive power, by torsion-free divisor cancellation. -/
theorem constantPowerQuotientMap_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (d.constantPowerQuotientMap n) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  change (QuotientGroup.map (unitPowers C n) (unitPowers K n)
    (Units.map d.constants.toMonoidHom) _).ker = ⊥
  rw [QuotientGroup.ker_map, d.unitPowers_comap_constant hn,
    QuotientGroup.map_mk'_self]

end DivisorData

/-- In a finite field containing a unit of order `n`, the quotient of units
by `n`th powers has order `n`, by cyclicity of the actual finite unit group. -/
theorem card_unitPowerQuotient (F : Type*) [Field F] [Finite F]
    {n : ℕ} (ζ : Fˣ) (hζ : orderOf ζ = n) :
    Nat.card (UnitPowerQuotient F n) = n := by
  change (unitPowers F n).index = n
  unfold unitPowers
  rw [IsCyclic.index_powMonoidHom_range]
  exact Nat.gcd_eq_right (hζ ▸ orderOf_dvd_natCard ζ)

end Field
