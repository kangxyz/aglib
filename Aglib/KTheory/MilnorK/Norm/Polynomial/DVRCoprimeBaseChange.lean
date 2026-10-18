/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DVRRamificationDegree

/-!
# Coprime base change of actual DVR ramification

In a commuting square of finite integral-closure DVR extensions, coprime
fraction-field degrees preserve the literal ramification exponent and residue
field degree. The exponent relation is proved from the four uniformizer
equations, not supplied as a ramification or norm-residue compatibility axiom.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open IsLocalRing IsDiscreteValuationRing.NormValuation

private theorem uniformizer_exponent_eq
    (U D : Type*) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Field D] [Algebra U D] [IsFractionRing U D]
    {ρ : U} (hρ : Irreducible ρ) (u v : Uˣ) (r s : ℕ)
    (h : (u : U) * ρ ^ r = (v : U) * ρ ^ s) : r = s := by
  have hu : Units.map (algebraMap U D).toMonoidHom u * uniformizerUnit U D hρ ^ r =
      Units.map (algebraMap U D).toMonoidHom v * uniformizerUnit U D hρ ^ s := by
    apply Units.ext
    change algebraMap U D (u : U) * algebraMap U D ρ ^ r =
      algebraMap U D (v : U) * algebraMap U D ρ ^ s
    simpa only [map_mul, map_pow] using congrArg (algebraMap U D) h
  have hv := congrArg (order U D) hu
  have hr : order U D (uniformizerUnit U D hρ ^ r) = (r : ℤ) := by
    simpa only [zpow_natCast, order_uniformizer, mul_one] using
      order_zpow U D (uniformizerUnit U D hρ) (r : ℤ)
  have hs : order U D (uniformizerUnit U D hρ ^ s) = (s : ℤ) := by
    simpa only [zpow_natCast, order_uniformizer, mul_one] using
      order_zpow U D (uniformizerUnit U D hρ) (s : ℤ)
  simpa only [order_mul, order_ringUnit, zero_add, hr, hs, Nat.cast_inj] using hv

/-- The two paths around an actual ring square give the same product of literal
uniformizer exponents. Only the final ring needs to be a DVR for this assertion. -/
theorem ramification_square_of_uniformizer_equations
    {R S T U D : Type*} [CommRing R] [CommRing S] [CommRing T]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Field D] [Algebra U D] [IsFractionRing U D]
    (j : R →+* S) (k : R →+* T) (l : S →+* U) (m : T →+* U)
    (hcomm : l.comp j = m.comp k)
    {π : R} {ϖ : S} {τ : T} {ρ : U} (hρ : Irreducible ρ)
    (u : Sˣ) (v : Tˣ) (w z : Uˣ) (e a b c : ℕ)
    (he : j π = (u : S) * ϖ ^ e) (ha : k π = (v : T) * τ ^ a)
    (hb : l ϖ = (w : U) * ρ ^ b) (hc : m τ = (z : U) * ρ ^ c) :
    e * b = a * c := by
  have h : (↑(Units.map l.toMonoidHom u * w ^ e) : U) * ρ ^ (e * b) =
      (↑(Units.map m.toMonoidHom v * z ^ a) : U) * ρ ^ (a * c) := by
    change (l (u : S) * (w : U) ^ e) * ρ ^ (e * b) =
      (m (v : T) * (z : U) ^ a) * ρ ^ (a * c)
    have hmaps := RingHom.congr_fun hcomm π
    change l (j π) = m (k π) at hmaps
    simpa only [he, ha, map_mul, map_pow, hb, hc, mul_pow, ← pow_mul,
      mul_assoc, Nat.mul_comm] using hmaps
  exact uniformizer_exponent_eq U D hρ _ _ _ _ h

private theorem coprime_square_exponents
    {p m e a b c : ℕ} (hcop : p.Coprime m)
    (he : e ∣ p) (ha : a ∣ m) (hb : b ∣ m) (hc : c ∣ p)
    (h : e * b = a * c) : e = c ∧ a = b := by
  have hec : e ∣ c := (hcop.of_dvd he ha).dvd_of_dvd_mul_left (by
    rw [← h]
    exact dvd_mul_right e b)
  have hce : c ∣ e := (hcop.of_dvd hc hb).dvd_of_dvd_mul_right (by
    rw [h]
    exact dvd_mul_left c a)
  have hab : a ∣ b := (hcop.symm.of_dvd ha he).dvd_of_dvd_mul_left (by
    rw [h]
    exact dvd_mul_right a c)
  have hba : b ∣ a := (hcop.symm.of_dvd hb hc).dvd_of_dvd_mul_right (by
    rw [← h]
    exact dvd_mul_left b e)
  exact ⟨Nat.dvd_antisymm hec hce, Nat.dvd_antisymm hab hba⟩

section ActualSquare

variable (R S T U F E L D : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Algebra R T] [Module.Finite R T] [Module.IsTorsionFree R T]
  [Algebra S U] [Module.Finite S U] [Module.IsTorsionFree S U]
  [Algebra T U] [Module.Finite T U] [Module.IsTorsionFree T U]
  [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]
  [Field E] [PerfectField E] [Algebra S E] [IsFractionRing S E]
  [Field L] [PerfectField L] [Algebra T L] [IsFractionRing T L]
  [Field D] [Algebra U D] [IsFractionRing U D]
  [Algebra F E] [Algebra R E] [IsScalarTower R F E] [IsScalarTower R S E]
  [Algebra F L] [Algebra R L] [IsScalarTower R F L] [IsScalarTower R T L]
  [Algebra E D] [Algebra S D] [IsScalarTower S E D] [IsScalarTower S U D]
  [Algebra L D] [Algebra T D] [IsScalarTower T L D] [IsScalarTower T U D]
  [Algebra F D] [IsScalarTower F E D] [IsScalarTower F L D]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  [IsIntegralClosure T R L] [FiniteDimensional F L]
  [IsIntegralClosure U S D] [FiniteDimensional E D]
  [IsIntegralClosure U T D] [FiniteDimensional L D]

/-- In an actual coprime degree square, the two opposite ramification
exponents and residue-field degrees agree. The top field degree is an actual
finrank equality; its companion equality is derived from the field tower law.
All four DVR degree formulas and the uniformizer exponent relation are proved
from the supplied integral-closure and literal uniformizer data. -/
theorem ramification_residue_finrank_eq_of_coprime_baseChange
    (hcomm : (algebraMap S U).comp (algebraMap R S) =
      (algebraMap T U).comp (algebraMap R T))
    (hdegree : Module.finrank L D = Module.finrank F E)
    (hcop : (Module.finrank F E).Coprime (Module.finrank F L))
    {π : R} {ϖ : S} {τ : T} {ρ : U}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (hτ : Irreducible τ) (hρ : Irreducible ρ)
    (u : Sˣ) (v : Tˣ) (w z : Uˣ) (e a b c : ℕ)
    (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (ha : algebraMap R T π = (v : T) * τ ^ a)
    (hb : algebraMap S U ϖ = (w : U) * ρ ^ b)
    (hc : algebraMap T U τ = (z : U) * ρ ^ c) :
    c = e ∧ b = a ∧
      Module.finrank (ResidueField T) (ResidueField U) =
        Module.finrank (ResidueField R) (ResidueField S) ∧
      Module.finrank (ResidueField S) (ResidueField U) =
        Module.finrank (ResidueField R) (ResidueField T) := by
  have hdegree' : Module.finrank E D = Module.finrank F L := by
    apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos : 0 < Module.finrank F E)
    calc
      Module.finrank F E * Module.finrank E D = Module.finrank F D :=
        Module.finrank_mul_finrank F E D
      _ = Module.finrank F L * Module.finrank L D :=
        (Module.finrank_mul_finrank F L D).symm
      _ = Module.finrank F E * Module.finrank F L := by rw [hdegree, Nat.mul_comm]
  have hRS := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R S F E hπ hϖ u e he
  have hRT := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R T F L hπ hτ v a ha
  have hSU := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    S U E D hϖ hρ w b hb
  have hTU := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    T U L D hτ hρ z c hc
  rw [hdegree'] at hSU
  rw [hdegree] at hTU
  have htower := ramification_square_of_uniformizer_equations (D := D)
    (algebraMap R S) (algebraMap R T) (algebraMap S U) (algebraMap T U)
    hcomm hρ u v w z e a b c he ha hb hc
  obtain ⟨hec, hab⟩ := coprime_square_exponents hcop
    ⟨_, hRS⟩ ⟨_, hRT⟩ ⟨_, hSU⟩ ⟨_, hTU⟩ htower
  have hepos : 0 < e := by
    have hpos : 0 < Module.finrank F E := Module.finrank_pos
    rw [hRS] at hpos
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at hpos)
  have hapos : 0 < a := by
    have hpos : 0 < Module.finrank F L := Module.finrank_pos
    rw [hRT] at hpos
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at hpos)
  refine ⟨hec.symm, hab.symm, ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_left hepos
    calc
      e * Module.finrank (ResidueField T) (ResidueField U) = Module.finrank F E := by
        rw [hec, ← hTU]
      _ = e * Module.finrank (ResidueField R) (ResidueField S) := hRS
  · apply Nat.eq_of_mul_eq_mul_left hapos
    calc
      a * Module.finrank (ResidueField S) (ResidueField U) = Module.finrank F L := by
        rw [hab, ← hSU]
      _ = a * Module.finrank (ResidueField R) (ResidueField T) := hRT

end ActualSquare

end MilnorK.PolynomialNorm
