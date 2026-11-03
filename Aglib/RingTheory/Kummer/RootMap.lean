/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.RootBaseChange

/-! # Compatible maps of the original coefficient-changed root algebras

Specialize the native quotient map to the same original binomial under an
actual coefficient algebra map. Both roots remain the literal original
roots; no iterated-base-change root algebra or new evaluation is selected.
-/

@[expose] public noncomputable section

open Polynomial

namespace Algebra.Kummer

variable {R B C D : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra R D]

/-- The native quotient map induced by an actual compatible coefficient map. -/
def rootMap (φ : B →ₐ[R] C) (N : ℕ) (f : R) :
    RootAlgebra N (algebraMap R B f) →ₐ[R] RootAlgebra N (algebraMap R C f) :=
  AdjoinRoot.mapAlgHom φ _ _ (by
    have h : (rootPolynomial N (algebraMap R B f)).map φ =
        rootPolynomial N (algebraMap R C f) := by
      simp only [rootPolynomial, Polynomial.map_sub, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C]
      change X ^ N - Polynomial.C (φ (algebraMap R B f)) = _
      rw [φ.commutes]
    simpa only [h] using (dvd_refl (rootPolynomial N (algebraMap R C f))))

@[simp] theorem rootMap_root (φ : B →ₐ[R] C) (N : ℕ) (f : R) :
    rootMap φ N f (AdjoinRoot.root (rootPolynomial N (algebraMap R B f))) =
      AdjoinRoot.root (rootPolynomial N (algebraMap R C f)) := by
  simp only [rootMap, AdjoinRoot.coe_mapAlgHom, AdjoinRoot.map_root]

@[simp] theorem rootMap_algebraMap (φ : B →ₐ[R] C) (N : ℕ) (f : R) (b : B) :
    rootMap φ N f (algebraMap B (RootAlgebra N (algebraMap R B f)) b) =
      algebraMap C (RootAlgebra N (algebraMap R C f)) (φ b) := by
  simp only [rootMap, AdjoinRoot.coe_mapAlgHom, AdjoinRoot.algebraMap_eq, AdjoinRoot.map_of]
  rfl

/-- The entire coefficient triangle, before evaluation on elements. -/
theorem rootMap_comp_algebraMap (φ : B →ₐ[R] C) (N : ℕ) (f : R) :
    (rootMap φ N f).toRingHom.comp (algebraMap B (RootAlgebra N (algebraMap R B f))) =
      (algebraMap C (RootAlgebra N (algebraMap R C f))).comp φ.toRingHom := by
  ext b
  exact rootMap_algebraMap φ N f b

/-- The original root-base map is retained by the whole coefficient transition. -/
theorem rootMap_comp_rootBaseChangeHom (φ : B →ₐ[R] C) (N : ℕ) (f : R) :
    (rootMap φ N f).comp (rootBaseChangeHom B N f) = rootBaseChangeHom C N f := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, rootBaseChangeHom_root, rootMap_root]

/-- Composition uses the original composed coefficient map and the same roots. -/
theorem rootMap_comp (φ : B →ₐ[R] C) (ψ : C →ₐ[R] D) (N : ℕ) (f : R) :
    (rootMap ψ N f).comp (rootMap φ N f) = rootMap (ψ.comp φ) N f := by
  apply AdjoinRoot.algHom_ext'
  · ext b
    simp only [AlgHom.comp_apply, AdjoinRoot.coe_ofAlgHom]
    change rootMap ψ N f (rootMap φ N f (algebraMap B _ b)) =
      rootMap (ψ.comp φ) N f (algebraMap B _ b)
    simp only [rootMap_algebraMap, AlgHom.comp_apply]
  · simp only [AlgHom.comp_apply, rootMap_root]

end Algebra.Kummer
