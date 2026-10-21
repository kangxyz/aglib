/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.RingTheory.MvPowerSeries.FrobeniusLinearIndependent
public import Aglib.RingTheory.Localization.FrobeniusLinearIndependent
public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# General separability of the canonical power-series fraction extension

For every field, including imperfect fields, the canonical extension from
the rational-function field to the fraction field of multivariate power series
is transcendental-separable. The action is the native fraction-ring lift.
-/

@[expose] public noncomputable section

namespace MvPowerSeries

/-- The canonical coefficient-polynomial embedding is faithful. -/
lemma faithfulSMul_mvPolynomial (k σ : Type*) [Field k] :
    FaithfulSMul (MvPolynomial σ k) (MvPowerSeries σ k) := by
  apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
  intro x y h
  apply MvPolynomial.coe_injective σ k
  simpa [algebraMap_apply'] using h

/-- The canonical rational-function action on the fraction field of series.
This is exactly native fraction-ring lifting of the polynomial embedding. -/
abbrev fractionFieldAlgebra (k σ : Type*) [Field k] :
    Algebra (FractionRing (MvPolynomial σ k)) (FractionRing (MvPowerSeries σ k)) := by
  let := faithfulSMul_mvPolynomial k σ
  exact FractionRing.liftAlgebra (MvPolynomial σ k) (FractionRing (MvPowerSeries σ k))

/-- General separability over the rational-function field, for its actual
compatible action. No perfectness hypothesis and no algebraicity assertion. -/
lemma isTranscendentalSeparable_fractionRing_of_tower
    (k σ : Type*) [Field k]
    [Algebra (FractionRing (MvPolynomial σ k)) (FractionRing (MvPowerSeries σ k))]
    [IsScalarTower (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))
      (FractionRing (MvPowerSeries σ k))] :
    Algebra.IsTranscendentalSeparable (FractionRing (MvPolynomial σ k))
      (FractionRing (MvPowerSeries σ k)) := by
  classical
  let P := MvPolynomial σ k
  let S := MvPowerSeries σ k
  let : IsDomain S := NoZeroDivisors.to_isDomain S
  let F := FractionRing P
  let L := FractionRing S
  refine ⟨fun E hE => ?_⟩
  let := hE
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · let : CharZero F := charZero_of_injective_ringHom
      (RingHom.injective (algebraMap k F))
    infer_instance
  let : ExpChar k p := .prime hp.out
  let : ExpChar F p := expChar_of_injective_ringHom
    (RingHom.injective (algebraMap k F)) p
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      (k := F) (K := E) p hp.out (fun s hs => by
        have ht := IsFractionRing.linearIndependent_pow_of_domain
          (R := P) (S := S) (F := F) (L := L) p
          (fun f hf => linearIndependent_pow_over_mvPolynomial p hp.out.ne_zero f hf)
          (fun i : s => (i.val : L))
          (hs.map' E.val.toLinearMap (LinearMap.ker_eq_bot.mpr E.val.injective))
        apply LinearIndependent.of_comp E.val.toLinearMap
        change LinearIndependent F (E.val.toLinearMap ∘ fun i : s => (i : E) ^ p)
        have heq : (E.val.toLinearMap ∘ fun i : s => (i : E) ^ p) =
            (fun i : s => (i.val : L) ^ p) := by
          funext i
          exact map_pow E.val i.val p
        rw [heq]
        exact ht)
  exact ⟨(s : Set E), hs, hsep⟩

/-- Unconditional arbitrary-field supplier for the canonical extension
Frac(k[X]) → Frac(k[[X]]). -/
lemma isTranscendentalSeparable_fractionRing (k σ : Type*) [Field k] :
    let := fractionFieldAlgebra k σ
    Algebra.IsTranscendentalSeparable (FractionRing (MvPolynomial σ k))
      (FractionRing (MvPowerSeries σ k)) := by
  let := faithfulSMul_mvPolynomial k σ
  let := fractionFieldAlgebra k σ
  let : IsScalarTower (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))
      (FractionRing (MvPowerSeries σ k)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  exact isTranscendentalSeparable_fractionRing_of_tower k σ

end MvPowerSeries
