/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod

/-!
# Multiplication characteristic polynomials under an actual tensor decomposition

The original multiplication operator is transported along the literal scalar
extension and the supplied algebra equivalence. Finite-product multiplicativity
is proved by finite-type induction from binary block-diagonal multiplicativity.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

variable {k : Type*} [Field k]

/-- Multiplication characteristic polynomials are invariant under an actual
algebra equivalence. -/
theorem charpoly_lmul_algEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [FiniteDimensional k A] [FiniteDimensional k B] (e : A ≃ₐ[k] B) (a : A) :
    (lmul k B (e a)).charpoly = (lmul k A a).charpoly := by
  have h : e.toLinearEquiv.conj (lmul k A a) = lmul k B (e a) := by
    ext x
    simp
  rw [← h, LinearEquiv.charpoly_conj]

/-- Binary product multiplication has the product characteristic polynomial. -/
theorem charpoly_lmul_prod
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [FiniteDimensional k A] [FiniteDimensional k B] (a : A × B) :
    (lmul k (A × B) a).charpoly =
      (lmul k A a.1).charpoly * (lmul k B a.2).charpoly := by
  have h : lmul k (A × B) a = (lmul k A a.1).prodMap (lmul k B a.2) := by
    ext x <;> rfl
  rw [h, LinearMap.charpoly_prodMap]

/-- The characteristic polynomial of actual multiplication on a dependent
finite product is the product of its factor characteristic polynomials. -/
theorem charpoly_lmul_pi : ∀ {ι : Type*} [Fintype ι]
    (D : ι → Type*) [∀ i, CommRing (D i)] [∀ i, Algebra k (D i)]
    [∀ i, FiniteDimensional k (D i)] (a : ∀ i, D i),
    (lmul k (∀ i, D i) a).charpoly = ∏ i, (lmul k (D i) (a i)).charpoly := by
  classical
  apply Fintype.induction_empty_option
  · intro α β _ e IH D _ _ _ a
    let _ : Fintype α := .ofEquiv β e.symm
    let E := AlgEquiv.piCongrLeft k D e
    rw [← charpoly_lmul_algEquiv E.symm a, IH]
    exact e.prod_comp (fun i ↦ (lmul k (D i) (a i)).charpoly)
  · intro D _ _ _ a
    have h : lmul k (∀ i : PEmpty, D i) a = 0 := Subsingleton.elim _ _
    simp [h, Module.finrank_zero_of_subsingleton]
  · intro ι _ IH D _ _ _ a
    let E : (∀ i, D i) ≃ₐ[k] D none × (∀ i, D (some i)) :=
      AlgEquiv.ofRingEquiv (f := RingEquiv.piOptionEquivProd) (by intro; rfl)
    rw [← charpoly_lmul_algEquiv E a, charpoly_lmul_prod, IH]
    rw [Fintype.prod_option]
    rfl

/-- A supplied tensor-product decomposition gives the characteristic-polynomial
product for the literal images of `1 ⊗ b`. Neither separability nor infinitude of
the scalar field is required. -/
theorem map_charpoly_lmul_eq_prod_tensor
    {F E L : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [FiniteDimensional F E]
    {ι : Type*} [Fintype ι] (D : ι → Type*) [∀ i, Field (D i)]
    [∀ i, Algebra L (D i)] [∀ i, FiniteDimensional L (D i)]
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (b : E) :
    ((lmul F E b).charpoly).map (algebraMap F L) =
      ∏ i, (lmul L (D i) ((ε (1 ⊗ₜ[F] b)) i)).charpoly := by
  rw [← LinearMap.charpoly_baseChange, Algebra.baseChange_lmul,
    ← charpoly_lmul_algEquiv ε, charpoly_lmul_pi]

end Algebra
