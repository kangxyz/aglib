/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# Restricting formal substitution to a coordinate subspace

The native `killCompl` map sets all variables outside an embedding to zero.
It commutes with genuine formal substitution. This coefficientwise identity
allows a triangular coordinate change followed by restriction to its pivot
axis to be compared with weighted specialization.
-/

@[expose] public section

namespace MvPowerSeries

variable {R σ τ υ : Type*} [CommRing R] [Finite σ]

lemma HasSubst.killCompl {a : σ → MvPowerSeries υ R} (ha : HasSubst a)
    (e : τ ↪ υ) : HasSubst (fun i ↦ killCompl e (a i)) := by
  apply hasSubst_of_constantCoeff_nilpotent
  intro i
  simpa only [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl,
    Finsupp.embDomain_zero] using ha.const_coeff i

/-- Coordinate-subspace restriction commutes with convergent formal substitution. -/
theorem killCompl_subst (e : τ ↪ υ) {a : σ → MvPowerSeries υ R}
    (ha : HasSubst a) (f : MvPowerSeries σ R) :
    killCompl e (subst a f) = subst (fun i ↦ killCompl e (a i)) f := by
  classical
  ext d
  rw [coeff_killCompl, coeff_subst ha, coeff_subst (ha.killCompl e)]
  apply finsum_congr
  intro b
  congr 1
  rw [← coeff_killCompl]
  congr 1
  simp only [map_finsuppProd, map_pow]

end MvPowerSeries
