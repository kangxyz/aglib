/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.Independence
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Actual finite-extension Milnor norms in characteristic zero

A native primitive-element presentation defines an integer-linear norm on the
original field. General polynomial-presentation independence proves that every
other actual presentation gives the same map. No general tower law is asserted
by the definition or assumed in the choice-independence theorem.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial PolynomialResidue PolynomialNorm

variable (k E : Type*) [Field k] [CharZero k] [Field E]
  [Algebra k E] [FiniteDimensional k E]

/-- A chosen native primitive-element polynomial of the actual finite field. -/
def finiteNormPolynomial : MonicIrreducible k :=
  let pb := Field.powerBasisOfFiniteOfSeparable k E
  ⟨minpoly k pb.gen, minpoly.monic pb.isIntegral_gen, minpoly.irreducible pb.isIntegral_gen⟩

/-- The chosen presentation is an actual equivalence with the original field. -/
def finiteNormPresentation : AdjoinRoot (finiteNormPolynomial k E).val ≃ₐ[k] E :=
  let pb := Field.powerBasisOfFiniteOfSeparable k E
  AdjoinRoot.equiv' (finiteNormPolynomial k E).val pb
    (by
      change aeval (AdjoinRoot.root (finiteNormPolynomial k E).val)
        (finiteNormPolynomial k E).val = 0
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
    (minpoly.aeval k pb.gen)

/-- The actual finite-extension norm, defined on the original Milnor group. -/
def finiteExtensionNorm (n : ℕ) : K E n →ₗ[ℤ] K k n :=
  (polynomialNorm n (finiteNormPolynomial k E)).comp
    (map n (finiteNormPresentation k E).symm.toRingHom)

/-- Every actual polynomial presentation computes the same finite-extension norm. -/
theorem finiteExtensionNorm_map_presentation (n : ℕ) (p : MonicIrreducible k)
    (ε : AdjoinRoot p.val ≃ₐ[k] E) (x : K (AdjoinRoot p.val) n) :
    finiteExtensionNorm k E n (map n ε.toRingHom x) = polynomialNorm n p x := by
  unfold finiteExtensionNorm
  rw [LinearMap.comp_apply,
    ← LinearMap.comp_apply (map n (finiteNormPresentation k E).symm.toRingHom), ← map_comp]
  exact polynomialNorm_map_algEquiv n p (finiteNormPolynomial k E)
    (ε.trans (finiteNormPresentation k E).symm) x

/-- The complete original-map presentation comparison. -/
theorem finiteExtensionNorm_comp_map_presentation (n : ℕ) (p : MonicIrreducible k)
    (ε : AdjoinRoot p.val ≃ₐ[k] E) :
    (finiteExtensionNorm k E n).comp (map n ε.toRingHom) = polynomialNorm n p := by
  apply LinearMap.ext
  exact finiteExtensionNorm_map_presentation k E n p ε

/-- The norm equals the original polynomial norm transported by any presentation. -/
theorem finiteExtensionNorm_eq_presentation (n : ℕ) (p : MonicIrreducible k)
    (ε : AdjoinRoot p.val ≃ₐ[k] E) :
    finiteExtensionNorm k E n = (polynomialNorm n p).comp (map n ε.symm.toRingHom) := by
  apply LinearMap.ext
  intro x
  have h := finiteExtensionNorm_map_presentation k E n p ε (map n ε.symm.toRingHom x)
  rw [← LinearMap.comp_apply (map n ε.toRingHom), ← map_comp] at h
  have he : ε.toRingHom.comp ε.symm.toRingHom = RingHom.id E := by
    apply RingHom.ext
    exact ε.apply_symm_apply
  rw [he, map_id, LinearMap.id_apply] at h
  exact h

/-- The original coefficient restriction followed by norm is the actual degree. -/
theorem finiteExtensionNorm_map_constants (n : ℕ) (x : K k n) :
    finiteExtensionNorm k E n (map n (algebraMap k E) x) =
      (Module.finrank k E : ℤ) • x := by
  unfold finiteExtensionNorm
  have hc : (finiteNormPresentation k E).symm.toRingHom.comp (algebraMap k E) =
      algebraMap k (AdjoinRoot (finiteNormPolynomial k E).val) := by
    apply RingHom.ext
    exact (finiteNormPresentation k E).symm.commutes
  rw [LinearMap.comp_apply,
    ← LinearMap.comp_apply (map n (finiteNormPresentation k E).symm.toRingHom), ← map_comp, hc,
    polynomialNorm_map_constants]
  have hd : (finiteNormPolynomial k E).val.natDegree = Module.finrank k E := by
    let pb := Field.powerBasisOfFiniteOfSeparable k E
    change (minpoly k pb.gen).natDegree = Module.finrank k E
    rw [pb.natDegree_minpoly, pb.finrank]
  rw [hd]

end MilnorK
