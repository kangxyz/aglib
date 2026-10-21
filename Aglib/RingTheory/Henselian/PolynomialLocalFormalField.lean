/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalFormal
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Removing the coefficient completion over a field

The actual formal target has completed coefficients. This equivalence removes
that completion using the canonical completion equivalence over a field, and
preserves the original polynomial map. It does not identify the two coefficient
rings definitionally or assert any new separability theorem.
-/

@[expose] public section

noncomputable section

namespace PolynomialLocalRing

variable (k : Type*) [Field k] (n : ℕ)

/-- The actual completed-coefficient formal series ring over a field is
canonically equivalent to the series ring over the original field. -/
def formalSeriesFieldEquiv : FormalSeries k n ≃ₐ[k] MvPowerSeries (Fin n) k := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let ec := AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal k)
  exact
    { MvPowerSeries.mapAlgHom ec.symm.toAlgHom with
      invFun := MvPowerSeries.map ec.toRingHom
      left_inv := fun f => by
        apply MvPowerSeries.ext
        intro d
        exact ec.apply_symm_apply _
      right_inv := fun f => by
        apply MvPowerSeries.ext
        intro d
        exact ec.symm_apply_apply _ }

@[simp] theorem formalSeriesFieldEquiv_X (i : Fin n) :
    formalSeriesFieldEquiv k n (MvPowerSeries.X i) = MvPowerSeries.X i := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  change MvPowerSeries.map
    (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal k)).symm.toRingHom
      (MvPowerSeries.X i) = MvPowerSeries.X i
  exact MvPowerSeries.map_X _ i

/-- The coefficient transport commutes with the original polynomial map. -/
theorem formalSeriesFieldEquiv_comp_polynomialToFormalSeries :
    (formalSeriesFieldEquiv k n).toAlgHom.comp (polynomialToFormalSeries k n) =
      MvPolynomial.aeval (fun i : Fin n => (MvPowerSeries.X i : MvPowerSeries (Fin n) k)) := by
  apply MvPolynomial.algHom_ext
  intro i
  change formalSeriesFieldEquiv k n
    (MvPolynomial.aeval (fun j => (MvPowerSeries.X j : FormalSeries k n))
      (MvPolynomial.X i)) =
    MvPolynomial.aeval (fun j => (MvPowerSeries.X j : MvPowerSeries (Fin n) k))
      (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  exact formalSeriesFieldEquiv_X k n i

/-- The same square for the native polynomial algebra actions used by the
fraction-field extension, not merely an abstract coefficient map. -/
theorem formalSeriesFieldEquiv_algebraMap (p : MvPolynomial (Fin n) k) :
    formalSeriesFieldEquiv k n (algebraMap (MvPolynomial (Fin n) k) (FormalSeries k n) p) =
      algebraMap (MvPolynomial (Fin n) k) (MvPowerSeries (Fin n) k) p := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let ec := AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal k)
  apply MvPowerSeries.ext
  intro d
  change ec.symm (algebraMap k (AdicCompletion (IsLocalRing.maximalIdeal k) k)
    (p.coeff d)) = algebraMap k k (p.coeff d)
  exact ec.symm.commutes (p.coeff d)

/-- A fixed fraction field of ordinary series is also a fraction field of the
actual formal target, with precisely the transported coefficient action. -/
theorem isFractionRing_of_formalSeriesFieldEquiv (L : Type*) [Field L]
    [Algebra (MvPowerSeries (Fin n) k) L]
    [IsFractionRing (MvPowerSeries (Fin n) k) L] :
    let : Algebra (FormalSeries k n) L :=
      ((algebraMap (MvPowerSeries (Fin n) k) L).comp
        (formalSeriesFieldEquiv k n).toRingHom).toAlgebra
    IsFractionRing (FormalSeries k n) L := by
  let : Algebra (FormalSeries k n) L :=
    ((algebraMap (MvPowerSeries (Fin n) k) L).comp
      (formalSeriesFieldEquiv k n).toRingHom).toAlgebra
  exact IsFractionRing.of_ringEquiv_left (formalSeriesFieldEquiv k n).toRingEquiv
    (fun _ => rfl)

end PolynomialLocalRing
