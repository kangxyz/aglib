/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Tensor base change for literal bivariate root algebras

One construction supplies both duplicate source interfaces. The mapped
polynomial equality is explicit; neither monicity nor a curve is assumed.

Source: `R5Lab.Aglib.RingTheory.AdjoinRoot.BivariateTensor`.
Packet SHA-256:
`3577b0090268283adde5f1dfd3d4189af47fb1a27dc72389c4f2d23520721e56`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Polynomial
open scoped Polynomial TensorProduct
universe u

namespace AdjoinRoot

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma polynomialTensor_comp_includeRight :
    (polyEquivTensor' R S).symm.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : Polynomial R →ₐ[R] S ⊗[R] Polynomial R).toRingHom =
        Polynomial.mapRingHom (algebraMap R S) := by
  apply RingHom.ext
  intro p
  change (polyEquivTensor R S).symm (1 ⊗ₜ[R] p) = p.map (algebraMap R S)
  simp

/-- The tensor equivalence for a bivariate monic presentation, including its actual coefficients. -/
def bivariateTensorEquiv (p : Polynomial (Polynomial R))
    (q : Polynomial (Polynomial S))
    (h : p.map (Polynomial.mapRingHom (algebraMap R S)) = q) :
    S ⊗[R] AdjoinRoot p ≃ₐ[S] AdjoinRoot q :=
  (AdjoinRoot.tensorAlgEquiv p
    (p.map (Algebra.TensorProduct.includeRight :
      Polynomial R →ₐ[R] S ⊗[R] Polynomial R).toRingHom) rfl).trans
    (AdjoinRoot.mapAlgEquiv (polyEquivTensor' R S).symm _ q (by
      apply Associated.of_eq
      rw [Polynomial.map_map]
      change p.map ((polyEquivTensor' R S).symm.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          Polynomial R →ₐ[R] S ⊗[R] Polynomial R).toRingHom) = q
      rw [polynomialTensor_comp_includeRight, h]))


@[simp] lemma bivariateTensorEquiv_root (p : Polynomial (Polynomial R))
    (q : Polynomial (Polynomial S))
    (h : p.map (Polynomial.mapRingHom (algebraMap R S)) = q) :
    bivariateTensorEquiv p q h (1 ⊗ₜ[R] AdjoinRoot.root p) = AdjoinRoot.root q := by
  set_option backward.isDefEq.respectTransparency false in
    simp [bivariateTensorEquiv, AdjoinRoot.coe_mapAlgEquiv]

@[simp] lemma bivariateTensorEquiv_of (p : Polynomial (Polynomial R))
    (q : Polynomial (Polynomial S))
    (h : p.map (Polynomial.mapRingHom (algebraMap R S)) = q) (a : Polynomial R) :
    bivariateTensorEquiv p q h (1 ⊗ₜ[R] AdjoinRoot.of p a) =
      AdjoinRoot.of q (a.map (algebraMap R S)) := by
  set_option backward.isDefEq.respectTransparency false in
    simp [bivariateTensorEquiv, AdjoinRoot.coe_mapAlgEquiv]

end AdjoinRoot
