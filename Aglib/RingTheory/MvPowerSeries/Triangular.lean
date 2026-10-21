/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Triangular changes of formal power series coordinates

Fix one pivot variable. Adding a positive power of that variable to every
other variable gives an algebra automorphism of formal power series. Its
inverse subtracts the same powers. The exponent assigned to the pivot is
unused. The inverse identities use the native composition theorem for
convergent formal substitution, not algebra homomorphism extensionality on
variables. No hypothesis on the characteristic or cardinality of the
coefficient ring is needed.
-/

@[expose] public section

namespace MvPowerSeries

variable {R σ : Type*} [CommRing R] [Finite σ] [DecidableEq σ]

/-- The coordinate family adding pivot powers to the non-pivot variables. -/
noncomputable def triangularCoordinates (p : σ) (e : σ → ℕ) (i : σ) : MvPowerSeries σ R :=
  if i = p then X p else X i + X p ^ e i

/-- The coordinate family subtracting pivot powers from the non-pivot variables. -/
noncomputable def triangularInverseCoordinates (p : σ) (e : σ → ℕ) (i : σ) :
    MvPowerSeries σ R :=
  if i = p then X p else X i - X p ^ e i

lemma hasSubst_triangularCoordinates (p : σ) (e : σ → ℕ)
    (he : ∀ i, i ≠ p → 0 < e i) :
    HasSubst (triangularCoordinates (R := R) p e) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  by_cases hi : i = p
  · simp [triangularCoordinates, hi]
  · simp [triangularCoordinates, hi, (he i hi).ne']

lemma hasSubst_triangularInverseCoordinates (p : σ) (e : σ → ℕ)
    (he : ∀ i, i ≠ p → 0 < e i) :
    HasSubst (triangularInverseCoordinates (R := R) p e) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  by_cases hi : i = p
  · simp [triangularInverseCoordinates, hi]
  · simp [triangularInverseCoordinates, hi, (he i hi).ne']

/-- A triangular change of formal coordinates with an explicit inverse. -/
noncomputable def triangularAlgEquiv (p : σ) (e : σ → ℕ)
    (he : ∀ i, i ≠ p → 0 < e i) :
    MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R := by
  let ha := hasSubst_triangularCoordinates (R := R) p e he
  let hb := hasSubst_triangularInverseCoordinates (R := R) p e he
  have hab : (fun i ↦ substAlgHom hb (triangularCoordinates (R := R) p e i)) = X := by
    funext i
    by_cases hi : i = p
    · subst i
      simp only [triangularCoordinates, ite_true, substAlgHom_X,
        triangularInverseCoordinates]
    · simp only [triangularCoordinates, hi, ite_false, map_add, map_pow,
        substAlgHom_X, triangularInverseCoordinates, ite_true, sub_add_cancel]
  have hba : (fun i ↦ substAlgHom ha
      (triangularInverseCoordinates (R := R) p e i)) = X := by
    funext i
    by_cases hi : i = p
    · subst i
      simp only [triangularInverseCoordinates, ite_true, substAlgHom_X,
        triangularCoordinates]
    · simp only [triangularInverseCoordinates, hi, ite_false, map_sub, map_pow,
        substAlgHom_X, triangularCoordinates, ite_true, add_sub_cancel_right]
  refine
    { __ := substAlgHom ha
      invFun := substAlgHom hb
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    change substAlgHom hb (substAlgHom ha f) = f
    simp only [coe_substAlgHom]
    rw [subst_comp_subst_apply ha hb]
    have hab' : (fun i ↦ subst (triangularInverseCoordinates (R := R) p e)
        (triangularCoordinates (R := R) p e i)) = X := by
      simpa only [coe_substAlgHom] using hab
    rw [hab', subst_self]
    rfl
  · intro f
    change substAlgHom ha (substAlgHom hb f) = f
    simp only [coe_substAlgHom]
    rw [subst_comp_subst_apply hb ha]
    have hba' : (fun i ↦ subst (triangularCoordinates (R := R) p e)
        (triangularInverseCoordinates (R := R) p e i)) = X := by
      simpa only [coe_substAlgHom] using hba
    rw [hba', subst_self]
    rfl

/-- The forward change fixes the pivot and adds its powers to other variables. -/
@[simp] theorem triangularAlgEquiv_X (p : σ) (e : σ → ℕ)
    (he : ∀ i, i ≠ p → 0 < e i) (i : σ) :
    triangularAlgEquiv (R := R) p e he (X i) =
      if i = p then X p else X i + X p ^ e i := by
  change substAlgHom (hasSubst_triangularCoordinates (R := R) p e he) (X i) = _
  exact substAlgHom_X _ i

/-- The inverse change fixes the pivot and subtracts its powers from other variables. -/
@[simp] theorem triangularAlgEquiv_symm_X (p : σ) (e : σ → ℕ)
    (he : ∀ i, i ≠ p → 0 < e i) (i : σ) :
    (triangularAlgEquiv (R := R) p e he).symm (X i) =
      if i = p then X p else X i - X p ^ e i := by
  change substAlgHom
    (hasSubst_triangularInverseCoordinates (R := R) p e he) (X i) = _
  exact substAlgHom_X _ i

end MvPowerSeries
