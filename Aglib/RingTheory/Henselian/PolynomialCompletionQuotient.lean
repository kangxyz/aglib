/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalRing
public import Aglib.RingTheory.MvPowerSeries.TruncIdeal
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.MvPowerSeries.Evaluation

/-! # Actual mixed polynomial quotient evaluation -/

@[expose] public section
noncomputable section

open IsLocalRing

namespace PolynomialLocalRing

universe u
variable (R : Type u) [CommRing R] [IsLocalRing R] (n k : ℕ)

/-- The original coefficient ideal maps into the polynomial origin ideal. -/
theorem map_maximalIdeal_C_le_originIdeal :
    (maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) ≤
      originIdeal R n := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  simpa [originIdeal] using hr

/-- Original coefficients modulo m^k map to the actual mixed polynomial quotient. -/
def coefficientQuotientMap : R ⧸ maximalIdeal R ^ k →+*
    MvPolynomial (Fin n) R ⧸ originIdeal R n ^ k :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp MvPolynomial.C) fun r hr => by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have h := Ideal.mem_map_of_mem (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) hr
    rw [Ideal.map_pow] at h
    exact (Ideal.pow_right_mono (map_maximalIdeal_C_le_originIdeal R n) k) h

/-- Completed coefficients evaluated in the actual mixed polynomial quotient. -/
def completedCoefficientQuotientMap : AdicCompletion (maximalIdeal R) R →+*
    MvPolynomial (Fin n) R ⧸ originIdeal R n ^ k :=
  (coefficientQuotientMap R n k).comp (AdicCompletion.evalₐ (maximalIdeal R) k).toRingHom

@[simp] theorem completedCoefficientQuotientMap_algebraMap (r : R) :
    completedCoefficientQuotientMap R n k
        (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
      Ideal.Quotient.mk _ (MvPolynomial.C r) := by
  change coefficientQuotientMap R n k
    (AdicCompletion.evalₐ (maximalIdeal R) k (algebraMap R _ r)) = _
  rw [(AdicCompletion.evalₐ (maximalIdeal R) k).commutes]
  rfl

/-- Evaluation of formal series in the nilpotent polynomial variables modulo q^k.
Discrete coefficient and target topologies are used only to construct the map. -/
def mixedQuotientEval :
    MvPowerSeries (Fin n) (AdicCompletion (maximalIdeal R) R) →+*
      MvPolynomial (Fin n) R ⧸ originIdeal R n ^ k := by
  let A := AdicCompletion (maximalIdeal R) R
  let Q := MvPolynomial (Fin n) R ⧸ originIdeal R n ^ k
  let : UniformSpace A := ⊥
  let : UniformSpace Q := ⊥
  let a : Fin n → Q := fun i => Ideal.Quotient.mk _ (MvPolynomial.X i)
  have ha : MvPowerSeries.HasEval a := by
    constructor
    · intro i
      apply IsNilpotent.isTopologicallyNilpotent
      refine ⟨k, ?_⟩
      change (Ideal.Quotient.mk (originIdeal R n ^ k) (MvPolynomial.X i)) ^ k = 0
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.pow_mem_pow
      simp [originIdeal]
    · simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]
  exact MvPowerSeries.eval₂Hom (φ := completedCoefficientQuotientMap R n k)
    continuous_of_discreteTopology ha

@[simp] theorem mixedQuotientEval_C (a : AdicCompletion (maximalIdeal R) R) :
    mixedQuotientEval R n k (MvPowerSeries.C a) = completedCoefficientQuotientMap R n k a := by
  let : UniformSpace (AdicCompletion (maximalIdeal R) R) := ⊥
  let : UniformSpace (MvPolynomial (Fin n) R ⧸ originIdeal R n ^ k) := ⊥
  unfold mixedQuotientEval
  rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]

@[simp] theorem mixedQuotientEval_X (i : Fin n) :
    mixedQuotientEval R n k (MvPowerSeries.X i) =
      Ideal.Quotient.mk _ (MvPolynomial.X i) := by
  let : UniformSpace (AdicCompletion (maximalIdeal R) R) := ⊥
  let : UniformSpace (MvPolynomial (Fin n) R ⧸ originIdeal R n ^ k) := ⊥
  unfold mixedQuotientEval
  rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]

variable [IsNoetherianRing R]

/-- The mixed maximal ideal maps into the image of the original polynomial origin ideal. -/
theorem maximalIdeal_le_comap_mixedQuotientEval :
    maximalIdeal (MvPowerSeries (Fin n) (AdicCompletion (maximalIdeal R) R)) ≤
      ((originIdeal R n).map (Ideal.Quotient.mk (originIdeal R n ^ k))).comap
        (mixedQuotientEval R n k) := by
  apply MvPowerSeries.maximalIdeal_le_comap_of_C_X
  · intro a ha
    rw [mixedQuotientEval_C]
    have hcoeff : maximalIdeal (AdicCompletion (maximalIdeal R) R) ≤
        ((originIdeal R n).map (Ideal.Quotient.mk (originIdeal R n ^ k))).comap
          (completedCoefficientQuotientMap R n k) := by
      rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap]
      intro r hr
      change completedCoefficientQuotientMap R n k (algebraMap R _ r) ∈
        (originIdeal R n).map (Ideal.Quotient.mk (originIdeal R n ^ k))
      rw [completedCoefficientQuotientMap_algebraMap]
      apply Ideal.mem_map_of_mem
      simpa [originIdeal] using hr
    exact hcoeff ha
  · intro i
    rw [mixedQuotientEval_X]
    apply Ideal.mem_map_of_mem
    simp [originIdeal]

/-- The formal mixed maximal-ideal power vanishes under nilpotent quotient evaluation. -/
theorem maximalIdeal_pow_le_ker_mixedQuotientEval :
    maximalIdeal (MvPowerSeries (Fin n) (AdicCompletion (maximalIdeal R) R)) ^ k ≤
      RingHom.ker (mixedQuotientEval R n k) := by
  apply (Ideal.map_eq_bot_iff_le_ker _).mp
  apply le_antisymm _ bot_le
  have h := Ideal.pow_right_mono
    (Ideal.map_le_iff_le_comap.mpr (maximalIdeal_le_comap_mixedQuotientEval R n k)) k
  rw [← Ideal.map_pow, ← Ideal.map_pow] at h
  simpa using h

/-- The inverse-direction actual finite-quotient homomorphism. -/
def mixedQuotientInv :
    (MvPowerSeries (Fin n) (AdicCompletion (maximalIdeal R) R) ⧸
      maximalIdeal (MvPowerSeries (Fin n) (AdicCompletion (maximalIdeal R) R)) ^ k) →+*
      MvPolynomial (Fin n) R ⧸ originIdeal R n ^ k :=
  Ideal.Quotient.lift _ (mixedQuotientEval R n k)
    (fun _ hx => maximalIdeal_pow_le_ker_mixedQuotientEval R n k hx)

local notation "Ahat" => AdicCompletion (maximalIdeal R) R
local notation "B" => MvPowerSeries (Fin n) Ahat
local notation "F" => (MvPolynomial.aeval (fun i : Fin n => (MvPowerSeries.X i : B)))

omit [IsNoetherianRing R] in
/-- Constant coefficients of the original polynomial map are the original
coefficient map followed by constant coefficients. -/
theorem constantCoeff_comp_polynomialToFormal :
    MvPowerSeries.constantCoeff.comp (F).toRingHom =
      (algebraMap R Ahat).comp MvPolynomial.constantCoeff := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [MvPowerSeries.algebraMap_apply]
  · intro i
    simp

/-- The original mixed polynomial ideal maps into the actual formal maximal ideal. -/
theorem originIdeal_le_comap_polynomialToFormal :
    originIdeal R n ≤ (maximalIdeal B).comap (F).toRingHom := by
  intro f hf
  have hc : MvPolynomial.constantCoeff f ∈ maximalIdeal R := hf
  have hmap : MvPowerSeries.constantCoeff (F f) =
      algebraMap R Ahat (MvPolynomial.constantCoeff f) :=
    RingHom.congr_fun (constantCoeff_comp_polynomialToFormal R n) f
  have hm : MvPowerSeries.constantCoeff (F f) ∈ maximalIdeal Ahat := by
    rw [hmap, AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ hc
  change F f ∈ maximalIdeal B
  simpa only [mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff] using hm

/-- The forward finite-quotient map induced by the original polynomial inclusion. -/
def mixedQuotientMap : (MvPolynomial (Fin n) R ⧸ originIdeal R n ^ k) →+*
    B ⧸ maximalIdeal B ^ k :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (F).toRingHom) fun f hf => by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have h := Ideal.mem_map_of_mem (F).toRingHom hf
    rw [Ideal.map_pow] at h
    exact (Ideal.pow_right_mono
      (Ideal.map_le_iff_le_comap.mpr (originIdeal_le_comap_polynomialToFormal R n)) k) h

@[simp] theorem mixedQuotientMap_mk (f : MvPolynomial (Fin n) R) :
    mixedQuotientMap R n k (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (F f) := rfl

@[simp] theorem mixedQuotientInv_mk (f : B) :
    mixedQuotientInv R n k (Ideal.Quotient.mk _ f) = mixedQuotientEval R n k f := rfl

omit [IsNoetherianRing R] in
/-- The inverse evaluation agrees with the polynomial quotient on original coefficients. -/
theorem mixedQuotientEval_comp_polynomialToFormal :
    (mixedQuotientEval R n k).comp (F).toRingHom = Ideal.Quotient.mk (originIdeal R n ^ k) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change mixedQuotientEval R n k (F (MvPolynomial.C r)) = _
    rw [MvPolynomial.aeval_C]
    rw [MvPowerSeries.algebraMap_apply]
    rw [mixedQuotientEval_C, completedCoefficientQuotientMap_algebraMap]
  · intro i
    change mixedQuotientEval R n k (F (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X, mixedQuotientEval_X]

/-- One inverse law, proved on the actual polynomial quotient. -/
theorem mixedQuotientInv_comp_map :
    (mixedQuotientInv R n k).comp (mixedQuotientMap R n k) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  exact mixedQuotientEval_comp_polynomialToFormal R n k

/-- Coefficient maximal-ideal powers map into formal maximal-ideal powers. -/
theorem map_coefficient_maximalIdeal_le :
    (maximalIdeal Ahat).map (MvPowerSeries.C : Ahat →+* B) ≤ maximalIdeal B := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change MvPowerSeries.C a ∈ maximalIdeal B
  simpa only [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_C] using ha

/-- The other composite fixes all completed constants, using actual finite
coefficient representatives rather than assuming a section of completion. -/
theorem mixedQuotientMap_eval_C (a : Ahat) :
    mixedQuotientMap R n k (mixedQuotientEval R n k (MvPowerSeries.C a)) =
      Ideal.Quotient.mk (maximalIdeal B ^ k) (MvPowerSeries.C a) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal R) k a)
  have he : completedCoefficientQuotientMap R n k a =
      Ideal.Quotient.mk (originIdeal R n ^ k) (MvPolynomial.C r) := by
    change coefficientQuotientMap R n k (AdicCompletion.evalₐ (maximalIdeal R) k a) = _
    rw [← hr]
    rfl
  rw [mixedQuotientEval_C, he, mixedQuotientMap_mk, MvPolynomial.aeval_C]
  rw [MvPowerSeries.algebraMap_apply]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
  have hc : algebraMap R Ahat r - a ∈ maximalIdeal Ahat ^ k := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    apply (AdicCompletion.evalₐ_eq_iff_sub_mem (maximalIdeal R)
      (maximalIdeal R).fg_of_isNoetherianRing k _ _).mp
    rw [(AdicCompletion.evalₐ (maximalIdeal R) k).commutes]
    exact hr
  have h := Ideal.mem_map_of_mem (MvPowerSeries.C : Ahat →+* B) hc
  rw [Ideal.map_pow] at h
  exact (Ideal.pow_right_mono (map_coefficient_maximalIdeal_le R n) k) h

/-- The other composite fixes every polynomial over the completed coefficients. -/
theorem mixedQuotientMap_eval_coe (f : MvPolynomial (Fin n) Ahat) :
    mixedQuotientMap R n k (mixedQuotientEval R n k (f : B)) =
      Ideal.Quotient.mk (maximalIdeal B ^ k) (f : B) := by
  have he : ((mixedQuotientMap R n k).comp (mixedQuotientEval R n k)).comp
      MvPolynomial.coeToMvPowerSeries.ringHom =
      (Ideal.Quotient.mk (maximalIdeal B ^ k)).comp MvPolynomial.coeToMvPowerSeries.ringHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa using mixedQuotientMap_eval_C R n k a
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPolynomial.coe_X]
      rw [mixedQuotientEval_X, mixedQuotientMap_mk, MvPolynomial.aeval_X]
  exact RingHom.congr_fun he f

/-- The second inverse law uses a finite truncation modulo the actual mixed
maximal ideal, not extensionality of arbitrary power-series algebra maps. -/
theorem mixedQuotientMap_comp_inv :
    (mixedQuotientMap R n k).comp (mixedQuotientInv R n k) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hv : Ideal.span (Set.range (MvPowerSeries.X : Fin n → B)) ≤ maximalIdeal B := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
  have ht : Ideal.Quotient.mk (maximalIdeal B ^ k) f =
      Ideal.Quotient.mk (maximalIdeal B ^ k) (f.truncTotal k : B) := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    exact (Ideal.pow_right_mono hv k) (MvPowerSeries.sub_truncTotal_mem_span_X_pow k f)
  change mixedQuotientMap R n k (mixedQuotientInv R n k (Ideal.Quotient.mk _ f)) =
    Ideal.Quotient.mk _ f
  rw [ht, mixedQuotientInv_mk]
  exact mixedQuotientMap_eval_coe R n k (f.truncTotal k)

/-- The actual mixed polynomial quotient and formal-series quotient are equivalent,
including zero variables and order zero. -/
def mixedQuotientRingEquiv :
    (MvPolynomial (Fin n) R ⧸ originIdeal R n ^ k) ≃+* B ⧸ maximalIdeal B ^ k :=
  RingEquiv.ofRingHom (mixedQuotientMap R n k) (mixedQuotientInv R n k)
    (mixedQuotientMap_comp_inv R n k) (mixedQuotientInv_comp_map R n k)

/-- The mixed finite-quotient equivalence respects the original coefficient ring. -/
def mixedQuotientAlgEquiv :
    (MvPolynomial (Fin n) R ⧸ originIdeal R n ^ k) ≃ₐ[R] B ⧸ maximalIdeal B ^ k where
  __ := mixedQuotientRingEquiv R n k
  commutes' r := by
    change mixedQuotientMap R n k (Ideal.Quotient.mk _ (MvPolynomial.C r)) = _
    rw [mixedQuotientMap_mk, MvPolynomial.aeval_C]
    rfl

@[simp] theorem mixedQuotientAlgEquiv_mk (f : MvPolynomial (Fin n) R) :
    mixedQuotientAlgEquiv R n k (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (F f) := rfl

end PolynomialLocalRing
