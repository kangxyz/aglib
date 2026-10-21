/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Splitting a separable field tensor product by evaluation

If every minimal polynomial of a finite separable extension `E/K` splits in
`L`, the canonical evaluation map `L ⊗[K] E → ((E →ₐ[K] L) → L)` is an algebra
equivalence. Chinese remainders supply surjectivity and the embedding count
supplies equality of dimensions. The original tensor evaluation is retained.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Algebra.IsSeparable

variable (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]

/-- Simultaneous evaluation of a scalar-extended field at all base embeddings. -/
def tensorProductEvaluation : L ⊗[K] E →ₐ[L] ((E →ₐ[K] L) → L) :=
  AlgHom.pi fun σ => AlgHom.liftEquiv K L E L σ

/-- The canonical evaluation formula on pure tensors. -/
theorem tensorProductEvaluation_tmul (a : L) (x : E) (σ : E →ₐ[K] L) :
    tensorProductEvaluation K E L (a ⊗ₜ[K] x) σ = a * σ x := rfl

variable [FiniteDimensional K E]

/-- Distinct embedding evaluations have comaximal kernels, so simultaneous
scalar-extended evaluation is onto. -/
theorem tensorProductEvaluation_surjective :
    Function.Surjective (tensorProductEvaluation K E L) := by
  classical
  let f : (E →ₐ[K] L) → (L ⊗[K] E →ₐ[L] L) := AlgHom.liftEquiv K L E L
  have hf (σ : E →ₐ[K] L) : Function.Surjective (f σ) := by
    intro a
    exact ⟨algebraMap L (L ⊗[K] E) a, (f σ).commutes a⟩
  have hker : Function.Injective (fun σ => RingHom.ker (f σ)) := by
    intro σ τ h
    change RingHom.ker (f σ) = RingHom.ker (f τ) at h
    apply (AlgHom.liftEquiv K L E L).injective
    apply AlgHom.ext
    intro x
    have hx : x - algebraMap L (L ⊗[K] E) (f σ x) ∈ RingHom.ker (f σ) := by
      simp only [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
    rw [h] at hx
    have he : f τ x - f σ x = 0 := by
      simpa only [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply] using hx
    exact (sub_eq_zero.mp he).symm
  let (σ : E →ₐ[K] L) : (RingHom.ker (f σ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (f σ) (hf σ)
  have hcop : Pairwise (fun σ τ => IsCoprime (RingHom.ker (f σ)) (RingHom.ker (f τ))) :=
    fun σ τ h => Ideal.isCoprime_of_isMaximal (hker.ne h)
  intro c
  obtain ⟨x, hx⟩ := Ideal.exists_forall_sub_mem_ideal hcop
    (fun σ => algebraMap L (L ⊗[K] E) (c σ))
  refine ⟨x, funext fun σ => ?_⟩
  have he : f σ x - c σ = 0 := by
    simpa only [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply] using hx σ
  exact sub_eq_zero.mp he

variable [Algebra.IsSeparable K E]

/-- The original tensor evaluation is bijective over a field splitting all
minimal polynomials of the finite separable extension. -/
theorem tensorProductEvaluation_bijective
    (hsplit : ∀ x : E, ((minpoly K x).map (algebraMap K L)).Splits) :
    Function.Bijective (tensorProductEvaluation K E L) := by
  classical
  let := Fintype.ofFinite (E →ₐ[K] L)
  have hcard : Nat.card (E →ₐ[K] L) = Module.finrank K E :=
    (Field.finSepDegree_eq_of_adjoin_splits K E L (IntermediateField.adjoin_univ K E)
      (fun x _ => ⟨Algebra.IsIntegral.isIntegral x, hsplit x⟩)).symm.trans
      (Field.finSepDegree_eq_finrank_of_isSeparable K E)
  have hdim : Module.finrank L (L ⊗[K] E) =
      Module.finrank L ((E →ₐ[K] L) → L) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card]
    exact hcard.symm.trans Nat.card_eq_fintype_card
  have hsurj := tensorProductEvaluation_surjective K E L
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (tensorProductEvaluation K E L).toLinearMap)).mpr hsurj, hsurj⟩

/-- The algebra equivalence whose forward map is simultaneous evaluation. -/
def tensorProductEquivPi
    (hsplit : ∀ x : E, ((minpoly K x).map (algebraMap K L)).Splits) :
    L ⊗[K] E ≃ₐ[L] ((E →ₐ[K] L) → L) :=
  AlgEquiv.ofBijective (tensorProductEvaluation K E L)
    (tensorProductEvaluation_bijective K E L hsplit)

/-- The splitting equivalence keeps the original tensor formula. -/
theorem tensorProductEquivPi_tmul
    (hsplit : ∀ x : E, ((minpoly K x).map (algebraMap K L)).Splits)
    (a : L) (x : E) (σ : E →ₐ[K] L) :
    tensorProductEquivPi K E L hsplit (a ⊗ₜ[K] x) σ = a * σ x := rfl

end Algebra.IsSeparable
