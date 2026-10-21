/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationEvaluation
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Splitting polynomial coefficients into the lower henselization

The original polynomial ring maps to polynomials over the lower actual
henselization by the same swap-based variable order as formal Weierstrass
normalization. Evaluation at the original last variable recovers exactly
the original map into the higher henselization. Thus coefficients obtained
by clearing localization denominators really enter the finite-reduction
consumer over the lower henselization, with no coefficient substitution.
-/

@[expose] public section

noncomputable section

namespace PolynomialLocalHenselization

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The original polynomial algebra maps through its localization into its
actual henselization. -/
def polynomialToHenselization (n : ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] PolynomialLocalHenselization R n :=
  (IsScalarTower.toAlgHom R (PolynomialLocalRing R n)
    (PolynomialLocalHenselization R n)).comp
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) (PolynomialLocalRing R n))

/-- The original last variable is isolated, and every remaining coefficient
is mapped through the original lower polynomial-local henselization. -/
def coefficientSplit (n : ℕ) : MvPolynomial (Fin (n + 1)) R →ₐ[R]
    Polynomial (PolynomialLocalHenselization R n) :=
  (Polynomial.mapAlgHom (polynomialToHenselization R n)).comp
    ((MvPolynomial.renameEquiv R (Equiv.swap 0 (Fin.last n))).trans
      (MvPolynomial.finSuccEquiv R n)).toAlgHom

@[simp] theorem coefficientSplit_X_last (n : ℕ) :
    coefficientSplit R n (MvPolynomial.X (Fin.last n)) = Polynomial.X := by
  simp [coefficientSplit, MvPolynomial.renameEquiv_apply,
    MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem coefficientSplit_X_lower (n : ℕ) (i : Fin n) :
    coefficientSplit R n (MvPolynomial.X (Equiv.swap 0 (Fin.last n) i.succ)) =
      Polynomial.C (polynomialToHenselization R n (MvPolynomial.X i)) := by
  simp [coefficientSplit, MvPolynomial.renameEquiv_apply,
    MvPolynomial.finSuccEquiv_X_succ]

/-- Evaluation of the split coefficients is literally the original higher
polynomial map, in the actual swap-based lower-variable order. -/
theorem polynomialEvaluation_comp_coefficientSplit (n : ℕ) :
    (polynomialEvaluation R n).comp (coefficientSplit R n) =
      polynomialToHenselization R (n + 1) := by
  apply MvPolynomial.algHom_ext
  intro j
  obtain ⟨k, rfl⟩ := (Equiv.swap 0 (Fin.last n)).surjective j
  refine Fin.cases ?_ (fun i => ?_) k
  · simp only [Equiv.swap_apply_left, AlgHom.comp_apply, coefficientSplit_X_last,
      polynomialEvaluation_X]
    rfl
  · change polynomialEvaluation R n
      (coefficientSplit R n
        (MvPolynomial.X (PolynomialLocalRing.lowerVariableEmbedding n i))) = _
    rw [PolynomialLocalRing.lowerVariableEmbedding_apply, coefficientSplit_X_lower,
      polynomialEvaluation_C]
    have h := AlgHom.congr_fun (variableInclusion_comp_of R n)
      (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) (MvPolynomial.X i))
    change variableInclusion R n (polynomialToHenselization R n (MvPolynomial.X i)) =
      algebraMap (PolynomialLocalRing R (n + 1))
        (PolynomialLocalHenselization R (n + 1))
        (PolynomialLocalRing.variableInclusion R n
          (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n)
            (MvPolynomial.X i))) at h
    rw [h, PolynomialLocalRing.variableInclusion_algebraMap, MvPolynomial.rename_X]
    rfl

/-- A system written with split coefficients becomes the original system
under the actual higher evaluation map. -/
theorem map_polynomialEvaluation_map_coefficientSplit (n : ℕ) {σ : Type*}
    (F : MvPolynomial σ (MvPolynomial (Fin (n + 1)) R)) :
    MvPolynomial.map (polynomialEvaluation R n).toRingHom
      (MvPolynomial.map (coefficientSplit R n).toRingHom F) =
        MvPolynomial.map (polynomialToHenselization R (n + 1)).toRingHom F := by
  rw [MvPolynomial.map_map]
  exact congrArg (fun f => MvPolynomial.map f F)
    (congrArg AlgHom.toRingHom (polynomialEvaluation_comp_coefficientSplit R n))

end PolynomialLocalHenselization
