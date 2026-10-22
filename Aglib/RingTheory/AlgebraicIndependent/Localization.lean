/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.MvPolynomial.Localization

/-! # Algebraic independence after localizing coefficients

The target and its actual coefficient tower are unchanged. The proof uses native
polynomial localization to clear denominators, without choosing coefficientwise
fractions or requiring a finite variable type.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace AlgebraicIndependent

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {R S K ι : Type*} [CommRing R] [CommRing S] [CommRing K]
variable [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

/-- Algebraic independence persists when the coefficient ring is localized in
an existing scalar tower. -/
theorem localization (M : Submonoid R) [IsLocalization M S] {x : ι → K}
    (hx : AlgebraicIndependent R x) : AlgebraicIndependent S x := by
  have he : (aeval x : MvPolynomial ι S →ₐ[S] K).toRingHom.comp
      (algebraMap (MvPolynomial ι R) (MvPolynomial ι S)) =
      (aeval x : MvPolynomial ι R →ₐ[R] K).toRingHom := by
    apply ringHom_ext
    · intro r
      change aeval x (MvPolynomial.map (algebraMap R S) (C r)) = aeval x (C r)
      rw [map_C, aeval_C, aeval_C, ← IsScalarTower.algebraMap_apply]
    · intro i
      change aeval x (MvPolynomial.map (algebraMap R S) (X i)) = aeval x (X i)
      rw [map_X, aeval_X, aeval_X]
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := M.map (C : R →+* MvPolynomial ι R)) (MvPolynomial ι S)
    (aeval x : MvPolynomial ι S →ₐ[S] K).toRingHom
  intro f hf
  have hf' : (aeval x : MvPolynomial ι R →ₐ[R] K) f = 0 := by
    change (aeval x : MvPolynomial ι R →ₐ[R] K).toRingHom f = 0
    rw [← RingHom.congr_fun he f]
    exact hf
  rw [hx.eq_zero_of_aeval_eq_zero f hf', map_zero]

end AlgebraicIndependent
