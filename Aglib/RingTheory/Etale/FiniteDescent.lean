/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Polynomial.Subring

/-!
# Finite etale models over finitely generated coefficient subalgebras

A finite etale algebra descends to a finite etale algebra over a finitely
generated coefficient subalgebra. The comparison is an actual algebra
equivalence with its scalar extension. No faithful-flatness hypothesis on
the coefficient inclusion is needed: flatness of the constructed etale
model makes its own map into the scalar extension injective.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Algebra.Etale

variable (R : Type w) [CommRing R] (A : Type u) [CommRing A]
  [Algebra R A] (B : Type v) [CommRing B] [Algebra A B]

/-- A finite etale algebra has a finite etale model over a finitely generated
coefficient subalgebra, with its actual scalar-extension equivalence. -/
theorem exists_subalgebra_fg_of_finite [Etale A B] [Module.Finite A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Etale A₀ B₀ ∧ Module.Finite A₀ B₀ ∧
        Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) := by
  classical
  let : IsStandardSmoothOfRelativeDimension 0 A B :=
    Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    IsStandardSmoothOfRelativeDimension.out (n := 0) (R := A) (S := B)
  choose p hp hz using fun i : ι ↦ _root_.IsIntegral.of_finite A (P.val i)
  let s : Set A := P.coeffs ∪ ⋃ i, (↑(p i).coeffs : Set A)
  have hs : s.Finite := P.finite_coeffs.union (Set.finite_iUnion fun i ↦ (p i).coeffs.finite_toSet)
  let A₀ : Subalgebra R A := Algebra.adjoin R s
  have hcoeff : P.coeffs ⊆ A₀ := fun x hx ↦
    Algebra.subset_adjoin (Set.mem_union_left _ hx)
  let : P.HasCoeffs A₀ := ⟨by simpa using hcoeff⟩
  let B₀ := P.ModelOfHasCoeffs A₀
  let P₀ := P.ofHasCoeffs A₀
  let : IsStandardSmoothOfRelativeDimension 0 A₀ B₀ :=
    ⟨ι, σ, inferInstance, inferInstance, P₀, hP⟩
  let : Etale A₀ B₀ :=
    Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr inferInstance
  let e : A ⊗[A₀] B₀ ≃ₐ[A] B := P.tensorModelOfHasCoeffsEquiv A₀
  let φ : B₀ →ₐ[A₀] B :=
    (e.restrictScalars A₀).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hφ : Function.Injective φ :=
    e.injective.comp (Algebra.TensorProduct.includeRight_injective Subtype.val_injective)
  have hφval (i : ι) : φ (P₀.val i) = P.val i := by
    change e (1 ⊗ₜ[A₀] (Ideal.Quotient.mk _ (MvPolynomial.X i))) = P.val i
    simpa only [map_one, one_mul, MvPolynomial.aeval_X] using
      (Algebra.Presentation.tensorModelOfHasCoeffsEquiv_tmul
        (P := P.toPresentation) A₀ (1 : A) (MvPolynomial.X i))
  have hint (i : ι) : _root_.IsIntegral A₀ (P.val i) := by
    have hc : (↑(p i).coeffs : Set A) ⊆ A₀.toSubring := by
      intro x hx
      exact Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, hx⟩))
    refine ⟨(p i).toSubring A₀.toSubring hc,
      (Polynomial.monic_toSubring _ _ _).mpr (hp i), ?_⟩
    have hmap : ((p i).toSubring A₀.toSubring hc).map (algebraMap A₀ A) = p i := by
      ext n
      simpa only [Polynomial.coeff_map, Subalgebra.algebraMap_apply] using
        (Polynomial.coeff_toSubring (p i) A₀.toSubring hc (n := n))
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap A (P.val i),
      hmap, Polynomial.aeval_def, hz i]
  have hint₀ (i : ι) : _root_.IsIntegral A₀ (P₀.val i) := by
    apply (isIntegral_algHom_iff φ hφ).mp
    rw [hφval]
    exact hint i
  have htop : Algebra.adjoin A₀ (Set.range P₀.val) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    exact P₀.aeval_val_surjective
  have hfg := fg_adjoin_of_finite (Set.finite_range P₀.val)
    (fun x ⟨i, hi⟩ ↦ hi ▸ hint₀ i)
  have hfinite : Module.Finite A₀ B₀ := Module.Finite.of_fg_top (by
    simpa only [htop, Algebra.top_toSubmodule] using hfg)
  exact ⟨A₀, B₀, inferInstance, inferInstance, ⟨hs.toFinset, by simp [A₀]⟩,
    inferInstance, hfinite, ⟨e.symm⟩⟩

end Algebra.Etale
