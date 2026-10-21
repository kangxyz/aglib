/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationTriangularFormal

/-!
# Pulling actual normalized solutions back to the original henselization

A solution of the coefficient-transformed system pulls back through the actual
inverse triangular source automorphism. The original formal square and ideal
transport preserve its prescribed approximation order. No abstract coordinate
compatibility hypothesis is added.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v w

namespace PolynomialLocalHenselization

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
variable (p : Fin n) (e : Fin n → ℕ) (he : ∀ i, i ≠ p → 0 < e i)

/-- Evaluation of the actual transformed system is the formal triangular transform
of the original evaluation. In particular, original formal solutions transform to solutions. -/
theorem eval₂_triangular_map {σ : Type v}
    (f : MvPolynomial σ (PolynomialLocalHenselization R n))
    (y : σ → PolynomialLocalRing.FormalSeries R n) :
    MvPolynomial.eval₂ (toFormalSeries R n).toRingHom
      (fun j => MvPowerSeries.triangularAlgEquiv
        (R := AdicCompletion (maximalIdeal R) R) p e he (y j))
      (MvPolynomial.map (triangularAlgEquiv R n p e he).toRingHom f) =
    MvPowerSeries.triangularAlgEquiv (R := AdicCompletion (maximalIdeal R) R) p e he
      (MvPolynomial.eval₂ (toFormalSeries R n).toRingHom y f) := by
  let α := triangularAlgEquiv R n p e he
  let β := MvPowerSeries.triangularAlgEquiv
    (R := AdicCompletion (maximalIdeal R) R) p e he
  have hcoeff : (toFormalSeries R n).toRingHom.comp α.toRingHom =
      β.toRingHom.comp (toFormalSeries R n).toRingHom := by
    apply RingHom.ext
    intro a
    exact AlgHom.congr_fun (toFormalSeries_comp_triangularAlgEquiv R n p e he) a
  change MvPolynomial.eval₂ (toFormalSeries R n).toRingHom (fun j => β (y j))
    (MvPolynomial.map α.toRingHom f) = β (MvPolynomial.eval₂ (toFormalSeries R n).toRingHom y f)
  rw [MvPolynomial.eval₂_map, hcoeff]
  exact (MvPolynomial.hom_eval₂ f (toFormalSeries R n).toRingHom β.toRingHom y).symm

/-- Actual solutions and precision for a normalized system pull back to the original
system through the actual inverse source coordinates. -/
theorem exists_solution_of_triangular_normalization {ι : Type v} {σ : Type w}
    (F : ι → MvPolynomial σ (PolynomialLocalHenselization R n))
    (y : σ → PolynomialLocalRing.FormalSeries R n) (c : ℕ)
    (x' : σ → PolynomialLocalHenselization R n)
    (hx : ∀ i, MvPolynomial.eval x'
      (MvPolynomial.map (triangularAlgEquiv R n p e he).toRingHom (F i)) = 0)
    (hclose : ∀ j, toFormalSeries R n (x' j) -
      MvPowerSeries.triangularAlgEquiv (R := AdicCompletion (maximalIdeal R) R) p e he (y j) ∈
        maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c) :
    ∃ x : σ → PolynomialLocalHenselization R n,
      (∀ i, MvPolynomial.eval x (F i) = 0) ∧
      ∀ j, toFormalSeries R n (x j) - y j ∈
        maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c := by
  let α := triangularAlgEquiv R n p e he
  let β := MvPowerSeries.triangularAlgEquiv
    (R := AdicCompletion (maximalIdeal R) R) p e he
  let x : σ → PolynomialLocalHenselization R n := fun j => α.symm (x' j)
  refine ⟨x, ?_, ?_⟩
  · intro i
    have hx' : MvPolynomial.eval₂ α.toRingHom x' (F i) = 0 := by
      simpa only [MvPolynomial.eval_map] using hx i
    have hz : α (MvPolynomial.eval x (F i)) = 0 := by
      have h := MvPolynomial.eval₂_comp α.toRingHom x (F i)
      change α (MvPolynomial.eval x (F i)) =
        MvPolynomial.eval₂ α.toRingHom (fun j => α (x j)) (F i) at h
      rw [h]
      simpa only [x, AlgEquiv.apply_symm_apply] using hx'
    exact α.injective (hz.trans α.map_zero.symm)
  · intro j
    have hm : (maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c).map β.symm.toRingHom =
        maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c := by
      change (maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c).map β.symm.toRingEquiv = _
      rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
    have h := Ideal.mem_map_of_mem β.symm.toRingHom (hclose j)
    rw [hm] at h
    change β.symm (toFormalSeries R n (x' j) - β (y j)) ∈
      maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c at h
    rw [map_sub, AlgEquiv.symm_apply_apply] at h
    change toFormalSeries R n ((triangularAlgEquiv R n p e he).symm (x' j)) - y j ∈ _
    rw [toFormalSeries_triangularAlgEquiv_symm]
    exact h

end PolynomialLocalHenselization
