/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.RingTheory.MvPowerSeries.CrossFieldFrobenius
public import Aglib.RingTheory.Localization.FrobeniusLinearIndependent
public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# General separability of the canonical power-series fraction extension

For a geometrically reduced coefficient-field extension k → K, the canonical
extension Frac(k[X]) → Frac(K[[X]]) is transcendental-separable.
The action is the native fraction-ring lift. No excellence equivalence is asserted.
-/

@[expose] public noncomputable section

namespace MvPowerSeries

/-- The canonical coefficient-polynomial embedding is faithful. -/
lemma faithfulSMul_mvPolynomial_coefficientExtension (k K σ : Type*)
    [Field k] [Field K] [Algebra k K] :
    FaithfulSMul (MvPolynomial σ k) (MvPowerSeries σ K) := by
  apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
  intro x y h
  apply MvPolynomial.coe_injective σ k
  have hm : MvPowerSeries.map (algebraMap k K) (x : MvPowerSeries σ k) =
      MvPowerSeries.map (algebraMap k K) (y : MvPowerSeries σ k) := by
    simpa only [algebraMap_apply'] using h
  apply MvPowerSeries.ext
  intro d
  apply (algebraMap k K).injective
  simpa only [coeff_map] using congrArg (coeff d) hm

/-- The canonical rational-function action on the fraction field of series.
This is exactly native fraction-ring lifting of the polynomial embedding. -/
abbrev crossFractionFieldAlgebra (k K σ : Type*) [Field k] [Field K] [Algebra k K] :
    Algebra (FractionRing (MvPolynomial σ k)) (FractionRing (MvPowerSeries σ K)) := by
  let := faithfulSMul_mvPolynomial_coefficientExtension k K σ
  exact FractionRing.liftAlgebra (MvPolynomial σ k) (FractionRing (MvPowerSeries σ K))

/-- General separability over the rational-function field, for its actual
compatible action. No perfectness hypothesis and no algebraicity assertion. -/
lemma isTranscendentalSeparable_crossFractionRing_of_tower
    (k K σ : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.IsGeometricallyReduced k K]
    [Algebra (FractionRing (MvPolynomial σ k)) (FractionRing (MvPowerSeries σ K))]
    [IsScalarTower (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))
      (FractionRing (MvPowerSeries σ K))] :
    Algebra.IsTranscendentalSeparable (FractionRing (MvPolynomial σ k))
      (FractionRing (MvPowerSeries σ K)) := by
  classical
  let P := MvPolynomial σ k
  let S := MvPowerSeries σ K
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
          (fun f hf =>
            linearIndependent_pow_over_mvPolynomial_of_geometricallyReduced p hp.out f hf)
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

/-- Canonical cross-coefficient supplier under intrinsic geometric reducedness
of the coefficient field extension. This does not assert excellence. -/
lemma isTranscendentalSeparable_crossFractionRing (k K σ : Type*)
    [Field k] [Field K] [Algebra k K] [Algebra.IsGeometricallyReduced k K] :
    let := crossFractionFieldAlgebra k K σ
    Algebra.IsTranscendentalSeparable (FractionRing (MvPolynomial σ k))
      (FractionRing (MvPowerSeries σ K)) := by
  let := faithfulSMul_mvPolynomial_coefficientExtension k K σ
  let := crossFractionFieldAlgebra k K σ
  let : IsScalarTower (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))
      (FractionRing (MvPowerSeries σ K)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  exact isTranscendentalSeparable_crossFractionRing_of_tower k K σ

end MvPowerSeries
