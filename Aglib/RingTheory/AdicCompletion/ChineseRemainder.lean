/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Powers
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Compatible finite Chinese remainder diagrams for completion

Every power of the product of a finite coprime ideal family has its actual
Chinese remainder decomposition. Transition maps retain literal residue
coordinates, the finite diagram needed for the semilocal completion product.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open scoped BigOperators
open Function

variable {R ι : Type*} [CommRing R] [Fintype ι]
  (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J))

include hJ in
/-- Coprimality identifies every product-power filtration with the corresponding
intersection of branch-power filtrations. -/
theorem prod_pow_eq_iInf (n : ℕ) : (∏ i, J i) ^ n = ⨅ i, J i ^ n := by
  classical
  rw [← Finset.prod_pow]
  simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := Finset.univ) (J := fun i => J i ^ n)
    (fun i _ j _ hij => (hJ hij).pow)

/-- Literal Chinese remainder map at filtration level `n`. -/
def quotientProdPowEquiv (n : ℕ) :
    (R ⧸ (∏ i, J i) ^ n) ≃+* ∀ i, R ⧸ J i ^ n :=
  (Ideal.quotEquivOfEq (prod_pow_eq_iInf J hJ n)).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i => J i ^ n)
      (fun _ _ hij => (hJ hij).pow))

@[simp]
theorem quotientProdPowEquiv_mk (n : ℕ) (r : R) (i : ι) :
    quotientProdPowEquiv J hJ n (Ideal.Quotient.mk ((∏ i, J i) ^ n) r) i =
      Ideal.Quotient.mk (J i ^ n) r := rfl

/-- The actual quotient transition maps commute with every CRT coordinate. -/
theorem quotientProdPowEquiv_factorPow {m n : ℕ} (hmn : m ≤ n)
    (x : R ⧸ (∏ i, J i) ^ n) (i : ι) :
    quotientProdPowEquiv J hJ m (Ideal.Quotient.factorPow (∏ i, J i) hmn x) i =
      Ideal.Quotient.factorPow (J i) hmn (quotientProdPowEquiv J hJ n x i) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- CRT is linear over the original ring as well as multiplicative. -/
def quotientProdPowAlgEquiv (n : ℕ) :
    (R ⧸ (∏ i, J i) ^ n) ≃ₐ[R] ∀ i, R ⧸ J i ^ n where
  __ := quotientProdPowEquiv J hJ n
  commutes' r := by ext i; rfl

/-- The actual projections from the product-ideal completion to each branch. -/
def prodCompletionToBranch (i : ι) :
    AdicCompletion (∏ i, J i) R →ₐ[R] AdicCompletion (J i) R :=
  reindexAlgHom (∏ i, J i) (J i) id monotone_id
    (fun n => (prod_pow_eq_iInf J hJ n).le.trans (iInf_le _ i))

@[simp]
theorem eval_prodCompletionToBranch (n : ℕ)
    (x : AdicCompletion (∏ i, J i) R) (i : ι) :
    evalₐ (J i) n (prodCompletionToBranch J hJ i x) =
      quotientProdPowEquiv J hJ n (evalₐ (∏ i, J i) n x) i := by
  rw [prodCompletionToBranch, evalₐ_reindexAlgHom]
  simp only [id_eq]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ (∏ i, J i) n x)
  rw [← hr]
  rfl

/-- Reconstruct a compatible product-ideal residue class from all branch classes. -/
def branchCompletionToProd :
    (∀ i, AdicCompletion (J i) R) →ₐ[R] AdicCompletion (∏ i, J i) R :=
  liftAlgHom (∏ i, J i)
    (fun n => (quotientProdPowAlgEquiv J hJ n).symm.toAlgHom.comp
      (AlgHom.pi fun i => (evalₐ (J i) n).comp (Pi.evalAlgHom R _ i)))
    (fun {m n} hmn => by
      apply AlgHom.ext
      intro x
      apply (quotientProdPowEquiv J hJ m).injective
      funext i
      change quotientProdPowEquiv J hJ m
          (Ideal.Quotient.factorPow (∏ i, J i) hmn
            ((quotientProdPowAlgEquiv J hJ n).symm
              (fun i => evalₐ (J i) n (x i)))) i = _
      rw [quotientProdPowEquiv_factorPow]
      change Ideal.Quotient.factorPow (J i) hmn
          ((quotientProdPowAlgEquiv J hJ n)
            ((quotientProdPowAlgEquiv J hJ n).symm (fun i => evalₐ (J i) n (x i))) i) =
        (quotientProdPowAlgEquiv J hJ m)
          ((quotientProdPowAlgEquiv J hJ m).symm (fun i => evalₐ (J i) m (x i))) i
      simp only [AlgEquiv.apply_symm_apply]
      exact factor_evalₐ (J i) hmn (x i))

@[simp]
theorem eval_branchCompletionToProd (n : ℕ) (x : ∀ i, AdicCompletion (J i) R) :
    evalₐ (∏ i, J i) n (branchCompletionToProd J hJ x) =
      (quotientProdPowAlgEquiv J hJ n).symm (fun i => evalₐ (J i) n (x i)) :=
  evalₐ_liftAlgHom _ _ _ _ _

/-- The full finite semilocal completion product, with no product-isomorphism
premise. Its maps are assembled from the literal CRT quotient diagrams. -/
def prodCompletionAlgEquiv :
    AdicCompletion (∏ i, J i) R ≃ₐ[R] ∀ i, AdicCompletion (J i) R :=
  AlgEquiv.ofAlgHom (AlgHom.pi (prodCompletionToBranch J hJ))
    (branchCompletionToProd J hJ)
    (by
      apply AlgHom.ext
      intro x
      funext i
      apply ext_evalₐ
      intro n
      simp only [AlgHom.comp_apply, AlgHom.pi_apply, AlgHom.id_apply,
        eval_prodCompletionToBranch, eval_branchCompletionToProd]
      exact congrFun ((quotientProdPowAlgEquiv J hJ n).apply_symm_apply _) i)
    (by
      apply AlgHom.ext
      intro x
      apply ext_evalₐ
      intro n
      simp only [AlgHom.comp_apply, AlgHom.id_apply, eval_branchCompletionToProd,
        AlgHom.pi_apply, eval_prodCompletionToBranch]
      exact (quotientProdPowAlgEquiv J hJ n).symm_apply_apply _)

@[simp]
theorem prodCompletionAlgEquiv_algebraMap (r : R) (i : ι) :
    prodCompletionAlgEquiv J hJ (algebraMap R (AdicCompletion (∏ i, J i) R) r) i =
      algebraMap R (AdicCompletion (J i) R) r :=
  congrFun ((prodCompletionAlgEquiv J hJ).commutes r) i

end AdicCompletion
