/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Pi

/-! Canonical finite-product dual and double-dual comparisons, retaining evaluation. -/

@[expose] public section

noncomputable section

namespace Module.Dual

variable (R M ι : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Finite ι]

/-- The dual of a finite product is the finite product of the duals. -/
def piEquiv : Dual R (ι → M) ≃ₗ[R] (ι → Dual R M) :=
  (Finsupp.linearEquivFunOnFinite R M ι).dualMap.trans (Finsupp.lsum R).symm

@[simp]
theorem piEquiv_apply [DecidableEq ι] (l : Dual R (ι → M)) (i : ι) (m : M) :
    piEquiv R M ι l i m = l (Pi.single i m) := by
  change l ((Finsupp.linearEquivFunOnFinite R M ι) (Finsupp.single i m)) = _
  rw [Finsupp.linearEquivFunOnFinite_single]

@[simp]
theorem piEquiv_symm_single [DecidableEq ι] (i : ι) (l : Dual R M) :
    (piEquiv R M ι).symm (Pi.single i l) = l.comp (LinearMap.proj i) := by
  apply (piEquiv R M ι).injective
  ext j m
  simp only [LinearEquiv.apply_symm_apply, piEquiv_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

/-- The double dual of a finite product, compared with the product of double duals. -/
def piDoubleDualEquiv : Dual R (Dual R (ι → M)) ≃ₗ[R] (ι → Dual R (Dual R M)) :=
  (piEquiv R M ι).dualMap.symm.trans (piEquiv R (Dual R M) ι)

/-- The finite-product comparison carries the original evaluation to coordinatewise evaluation. -/
@[simp]
theorem piDoubleDualEquiv_eval (x : ι → M) :
    piDoubleDualEquiv R M ι (eval R (ι → M) x) = fun i ↦ eval R M (x i) := by
  classical
  ext i l
  change piEquiv R (Dual R M) ι ((piEquiv R M ι).dualMap.symm
    (eval R (ι → M) x)) i l = l (x i)
  rw [piEquiv_apply, LinearEquiv.dualMap_symm]
  change ((piEquiv R M ι).symm (Pi.single i l)) x = l (x i)
  rw [piEquiv_symm_single]
  rfl

end Module.Dual
