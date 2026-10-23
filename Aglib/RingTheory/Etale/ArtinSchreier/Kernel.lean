/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.ArtinSchreier
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The split kernel algebra of the Artin--Schreier polynomial

For every commutative ring in which `p = 0`, the original quotient by
`X^p - X` is canonically the product of copies of the base indexed by `ZMod p`.
Its forward map evaluates at the literal constants `(i.val : R)`. The proof
uses the finite-field factorization and the Chinese remainder theorem, and
includes the zero ring without assuming exact characteristic `p` there.
-/

@[expose] public noncomputable section

open Polynomial
open scoped Function

namespace Algebra.ArtinSchreier

variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]

/-- The canonical residue-constant map only needs the literal equation `p = 0`.
Its characteristic parameter is `ringChar R`, including for the zero ring. -/
def residueScalarHom (hR : (p : R) = 0) : ZMod p →+* R :=
  ZMod.castHom (ringChar.dvd hR) R

@[simp]
theorem residueScalarHom_apply (hR : (p : R) = 0) (i : ZMod p) :
    residueScalarHom p hR i = (i.val : R) := by
  change ZMod.cast i = (i.val : R)
  exact (ZMod.natCast_val i).symm

/-- Distinct residue constants have unit difference, even in a trivial target ring. -/
theorem isUnit_residueScalar_sub (hR : (p : R) = 0) {i j : ZMod p} (hij : i ≠ j) :
    IsUnit ((i.val : R) - (j.val : R)) := by
  have h : IsUnit (i - j) := (sub_ne_zero.mpr hij).isUnit
  simpa only [map_sub, residueScalarHom_apply] using h.map (residueScalarHom p hR)

private theorem poly_zero_eq_prod_zmod :
    poly p (0 : ZMod p) = ∏ i : ZMod p, (X - C i) := by
  have hroots : (poly p (0 : ZMod p)).roots = Finset.univ.val := by
    simpa only [poly, map_zero, sub_zero, ZMod.card] using
      FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have hcard : (poly p (0 : ZMod p)).roots.card = (poly p (0 : ZMod p)).natDegree := by
    rw [hroots]
    simp only [Finset.card_val, Finset.card_univ, ZMod.card, poly, map_zero, sub_zero,
      FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) (Fact.out : p.Prime).one_lt]
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (poly_monic p (0 : ZMod p)) hcard
  rw [hroots] at h
  exact h.symm

/-- The actual kernel polynomial is the product of its original residue-constant factors. -/
theorem poly_zero_eq_prod (hR : (p : R) = 0) :
    poly p (0 : R) = ∏ i : ZMod p, (X - C (i.val : R)) := by
  have h := congrArg (Polynomial.map (residueScalarHom p hR)) (poly_zero_eq_prod_zmod p)
  simpa only [poly, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_zero, map_zero, Polynomial.map_prod,
    residueScalarHom_apply] using h

/-- The principal ideal of the original factor at the indicated residue constant. -/
def kernelFactorIdeal (i : ZMod p) : Ideal R[X] :=
  Ideal.span {X - C (i.val : R)}

/-- The original linear-factor ideals are pairwise coprime. -/
theorem kernelFactorIdeal_pairwise (hR : (p : R) = 0) :
    Pairwise (IsCoprime on kernelFactorIdeal (R := R) p) := by
  intro i j hij
  apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
  exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_residueScalar_sub p hR hij)

/-- The original defining ideal is the intersection of the residue-factor ideals. -/
theorem span_poly_zero_eq_iInf (hR : (p : R) = 0) :
    Ideal.span {poly p (0 : R)} = ⨅ i : ZMod p, kernelFactorIdeal (R := R) p i := by
  classical
  rw [poly_zero_eq_prod p hR, ← Ideal.prod_span_singleton]
  simpa only [kernelFactorIdeal, Finset.mem_univ, iInf_true] using
    (Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
      (J := kernelFactorIdeal (R := R) p)
      (fun i _ j _ hij => kernelFactorIdeal_pairwise p hR hij))

/-- Native CRT for the original factor ideals, retaining the base algebra structure. -/
def kernelQuotientInfAlgEquiv (hR : (p : R) = 0) :
    (R[X] ⧸ ⨅ i : ZMod p, kernelFactorIdeal (R := R) p i) ≃ₐ[R]
      ((i : ZMod p) → R[X] ⧸ kernelFactorIdeal (R := R) p i) :=
  { Ideal.quotientInfRingEquivPiQuotient (kernelFactorIdeal (R := R) p)
      (kernelFactorIdeal_pairwise p hR) with
    commutes' := fun r => by ext i; rfl }

/-- The original Artin--Schreier kernel algebra is the constant product algebra.
The forward map is the simultaneous evaluation at the original residue constants. -/
def kernelAlgEquiv (hR : (p : R) = 0) : RootAlgebra p (0 : R) ≃ₐ[R] (ZMod p → R) :=
  (Ideal.quotientEquivAlgOfEq R (span_poly_zero_eq_iInf p hR)).trans
    ((kernelQuotientInfAlgEquiv p hR).trans
      (AlgEquiv.piCongrRight fun i : ZMod p =>
        Polynomial.quotientSpanXSubCAlgEquiv (i.val : R)))

/-- On every original polynomial class, the forward coordinate is literal evaluation. -/
@[simp]
theorem kernelAlgEquiv_mk (hR : (p : R) = 0) (g : R[X]) (i : ZMod p) :
    kernelAlgEquiv p hR (AdjoinRoot.mk (poly p (0 : R)) g) i = g.eval (i.val : R) := by
  rfl

/-- The distinguished quotient root has the original residue constants as coordinates. -/
@[simp]
theorem kernelAlgEquiv_root (hR : (p : R) = 0) (i : ZMod p) :
    kernelAlgEquiv p hR (AdjoinRoot.root (poly p (0 : R))) i = (i.val : R) := by
  simpa only [AdjoinRoot.root, Polynomial.eval_X] using kernelAlgEquiv_mk p hR X i

/-- The splitting preserves every original base scalar in each coordinate. -/
theorem kernelAlgEquiv_algebraMap (hR : (p : R) = 0) (r : R) (i : ZMod p) :
    kernelAlgEquiv p hR (algebraMap R (RootAlgebra p (0 : R)) r) i = r := by
  exact congrFun ((kernelAlgEquiv p hR).commutes r) i

end Algebra.ArtinSchreier
