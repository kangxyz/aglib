/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.RationalCoefficientRoot

/-!
# Literal rational-function equivalences induced by coefficient equivalences

The forward and inverse maps are the original polynomial-local-residue
coefficient maps. An equivalence over a base field induces an equivalence over
its actual rational-function field, not a replacement scalar action.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc

attribute [local instance] Polynomial.algebra

namespace Polynomial.LocalResidue

variable {A B C : Type*} [Field A] [Field B] [Field C]

/-- Composition of literal coefficient maps on rational functions. -/
theorem fractionMap_comp (φ : A →+* B) (ψ : B →+* C) :
    (fractionMap ψ).comp (fractionMap φ) = fractionMap (ψ.comp φ) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors A[X])
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, fractionMap_polynomial, Polynomial.map_map]

/-- The literal coefficient map of the identity is the identity. -/
@[simp]
theorem fractionMap_id : fractionMap (RingHom.id A) = RingHom.id (RatFunc A) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors A[X])
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, fractionMap_polynomial, Polynomial.map_id, RingHom.id_apply]

/-- An actual coefficient equivalence gives mutually inverse literal fraction maps. -/
def fractionMapRingEquiv (φ : A ≃+* B) : RatFunc A ≃+* RatFunc B :=
  RingEquiv.ofRingHom (fractionMap φ.toRingHom) (fractionMap φ.symm.toRingHom)
    (by rw [fractionMap_comp]; simp)
    (by rw [fractionMap_comp]; simp)

theorem fractionMapRingEquiv_toRingHom (φ : A ≃+* B) :
    (fractionMapRingEquiv φ).toRingHom = fractionMap φ.toRingHom := rfl

theorem fractionMapRingEquiv_symm_toRingHom (φ : A ≃+* B) :
    (fractionMapRingEquiv φ).symm.toRingHom = fractionMap φ.symm.toRingHom := rfl

@[simp]
theorem fractionMapRingEquiv_apply (φ : A ≃+* B) (x : RatFunc A) :
    fractionMapRingEquiv φ x = fractionMap φ.toRingHom x := rfl

variable {k : Type*} [Field k] [Algebra k A] [Algebra k B]

/-- The induced equivalence uses the native scalar actions of `k(X)`. -/
def fractionMapAlgEquiv (φ : A ≃ₐ[k] B) : RatFunc A ≃ₐ[RatFunc k] RatFunc B where
  __ := fractionMapRingEquiv φ.toRingEquiv
  commutes' x := by
    change fractionMap φ.toRingHom (algebraMap (RatFunc k) (RatFunc A) x) = _
    rw [ratFunc_algebraMap_eq_fractionMap, ratFunc_algebraMap_eq_fractionMap]
    have h : φ.toRingHom.comp (algebraMap k A) = algebraMap k B := by
      ext a
      exact φ.commutes a
    change ((fractionMap φ.toRingHom).comp (fractionMap (algebraMap k A))) x = _
    rw [fractionMap_comp, h]

theorem fractionMapAlgEquiv_toRingHom (φ : A ≃ₐ[k] B) :
    (fractionMapAlgEquiv φ).toRingHom = fractionMap φ.toRingHom := rfl

theorem fractionMapAlgEquiv_symm_toRingHom (φ : A ≃ₐ[k] B) :
    (fractionMapAlgEquiv φ).symm.toRingHom = fractionMap φ.symm.toRingHom := rfl

end Polynomial.LocalResidue
