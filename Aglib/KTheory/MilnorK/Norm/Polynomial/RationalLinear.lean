/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalFunction

/-!
# The actual rational norm of a linear constant presentation

For a degree-one constant presentation the actual rational-function norm is
the coefficient map of its literal root evaluation. Consequently its finite
linear residue and infinity residue commute with the original coefficient
norm, in all Milnor degrees and every characteristic.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue
open MilnorK.K3.PolynomialNorm (rootEvaluation rootEvaluation_algebraMap rootEvaluation_root)
open scoped RatFunc

attribute [local instance] Polynomial.algebra

variable {k : Type*} [Field k] (p : MonicIrreducible k) (hp : p.val.natDegree = 1)

local instance : Fact (Irreducible (p.val.map (RatFunc.C : k →+* RatFunc k))) :=
  ⟨p.property.1.irreducible_map_ratFunc_C p.property.2⟩

@[simp]
theorem rationalCoefficientPolynomial_natDegree :
    (rationalCoefficientPolynomial p).val.natDegree = p.val.natDegree :=
  Polynomial.natDegree_map _

/-- Root evaluation after the actual rational root identification is literal
coefficient evaluation, not an abstract degree-one field isomorphism. -/
theorem rationalCoefficient_rootEvaluation_comp :
    (rootEvaluation (rationalCoefficientPolynomial p)
      ((rationalCoefficientPolynomial_natDegree p).trans hp)).comp
        (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom =
      fractionMap (rootEvaluation p hp) := by
  have hc : (fractionMap (rootEvaluation p hp)).comp
      (fractionMap (algebraMap k (AdjoinRoot p.val))) = RingHom.id (RatFunc k) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RatFunc.algebraMap_C, fractionMap_C,
        rootEvaluation_algebraMap, RingHom.id_apply]
    · simp only [RingHom.comp_apply, RatFunc.algebraMap_X, fractionMap_X, RingHom.id_apply]
  have h : (fractionMap (rootEvaluation p hp)).comp
      (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).toRingHom =
      rootEvaluation (rationalCoefficientPolynomial p)
        ((rationalCoefficientPolynomial_natDegree p).trans hp) := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro a
      change fractionMap (rootEvaluation p hp)
        ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
          (algebraMap (RatFunc k) (AdjoinRoot (p.val.map RatFunc.C)) a)) =
        rootEvaluation (rationalCoefficientPolynomial p)
          ((rationalCoefficientPolynomial_natDegree p).trans hp)
          (algebraMap (RatFunc k) (AdjoinRoot (rationalCoefficientPolynomial p).val) a)
      rw [AdjoinRoot.rationalCoefficientAlgEquiv_algebraMap,
        rootEvaluation_algebraMap]
      exact RingHom.congr_fun hc a
    · change fractionMap (rootEvaluation p hp)
        ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
          (AdjoinRoot.root (p.val.map RatFunc.C))) =
        rootEvaluation (rationalCoefficientPolynomial p)
          ((rationalCoefficientPolynomial_natDegree p).trans hp)
          (AdjoinRoot.root (rationalCoefficientPolynomial p).val)
      rw [AdjoinRoot.rationalCoefficientAlgEquiv_root, fractionMap_C,
        rootEvaluation_root, rootEvaluation_root]
      simp only [rationalCoefficientPolynomial, coeff_map, map_neg]
  apply RingHom.ext
  intro x
  have hx := RingHom.congr_fun h
    ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm x)
  change fractionMap (rootEvaluation p hp)
    ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)
      ((AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm x)) = _ at hx
  rw [AlgEquiv.apply_symm_apply] at hx
  exact hx.symm

/-- The original rational-function norm of a linear presentation is exactly
the Milnor map of coefficient root evaluation, including degree zero. -/
theorem rationalFunctionNorm_eq_map_rootEvaluation (n : ℕ) :
    rationalFunctionNorm n p = map n (fractionMap (rootEvaluation p hp)) := by
  unfold rationalFunctionNorm
  rw [polynomialNorm_eq_map_rootEvaluation n (rationalCoefficientPolynomial p)
    ((rationalCoefficientPolynomial_natDegree p).trans hp)]
  have h := congrArg (map n) (rationalCoefficient_rootEvaluation_comp p hp)
  unfold rationalCoefficientPolynomial at h ⊢
  rw [map_comp] at h
  exact h

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩
local instance : Fact (Irreducible (X : (AdjoinRoot p.val)[X])) := ⟨irreducible_X⟩

/-- The actual finite quotient residue square for a linear constant presentation. -/
theorem residueAt_X_rationalFunctionNorm_linear (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    residueAt (X : k[X]) n (rationalFunctionNorm (n + 1) p x) =
      map n (adjoinRootMap (rootEvaluation p hp) X X (by simp))
        (residueAt (X : (AdjoinRoot p.val)[X]) n x) := by
  rw [rationalFunctionNorm_eq_map_rootEvaluation p hp]
  apply residueAt_restrict_of_unramified
  simpa only [localRingMap_polynomial, Polynomial.map_X] using
    (irreducible_polynomial (X : k[X]))

include hp in
/-- Under the literal root-at-zero identifications the finite residue square
has the original polynomial norm on its coefficient-field side. -/
theorem residueAt_X_rationalFunctionNorm_linear_normalized (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (InfinityResidue.rootXEquiv k).toRingHom
        (residueAt (X : k[X]) n (rationalFunctionNorm (n + 1) p x)) =
      polynomialNorm n p
        (map n (InfinityResidue.rootXEquiv (AdjoinRoot p.val)).toRingHom
          (residueAt (X : (AdjoinRoot p.val)[X]) n x)) := by
  rw [residueAt_X_rationalFunctionNorm_linear p hp,
    polynomialNorm_eq_map_rootEvaluation n p hp]
  have h : (InfinityResidue.rootXEquiv k).toRingHom.comp
      (adjoinRootMap (rootEvaluation p hp) X X (by simp)) =
      (rootEvaluation p hp).comp
        (InfinityResidue.rootXEquiv (AdjoinRoot p.val)).toRingHom := by
    apply RingHom.ext
    intro a
    exact InfinityResidue.rootXEquiv_adjoinRootMap (rootEvaluation p hp) a
  rw [← LinearMap.comp_apply, ← map_comp, h, map_comp, LinearMap.comp_apply]

include hp in
/-- The actual infinity residue of the rational norm is the original
coefficient norm of the actual upper infinity residue. -/
theorem infinityResidue_rationalFunctionNorm_linear (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    InfinityResidue.residue k n (rationalFunctionNorm (n + 1) p x) =
      polynomialNorm n p (InfinityResidue.residue (AdjoinRoot p.val) n x) := by
  rw [rationalFunctionNorm_eq_map_rootEvaluation p hp, InfinityResidue.residue_restrict,
    polynomialNorm_eq_map_rootEvaluation n p hp]

end MilnorK.PolynomialNorm
