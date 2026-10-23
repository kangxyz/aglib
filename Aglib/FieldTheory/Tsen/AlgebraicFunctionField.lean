/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Tsen.FiniteFunctionField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Tsen's theorem for algebraic extensions of a rational function field

A form has finitely many coefficients. Adjoining them gives an actual finite
intermediate field, so the finite-extension theorem supplies its nonzero zero.
This includes infinite algebraic extensions without a cohomological continuity
assumption and retains the original homogeneous form under the field inclusion.
-/

@[expose] public section

namespace Field

/-- Every algebraic extension of `K(T)`, for algebraically closed `K`, is C₁. -/
theorem isC1_algebraic_ratFunc (K E : Type*) [Field K] [IsAlgClosed K] [Field E]
    [Algebra (RatFunc K) E] [Algebra.IsAlgebraic (RatFunc K) E] : IsC1 E := by
  classical
  intro n d p hd hdn hp
  let F := IntermediateField.adjoin (RatFunc K) (p.coeffs : Set E)
  let : FiniteDimensional (RatFunc K) F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let f : F →+* E := F.subtype
  have hpF : p ∈ Set.range (MvPolynomial.map f) := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    exact ⟨⟨x, IntermediateField.subset_adjoin (RatFunc K) _ hx⟩, rfl⟩
  obtain ⟨q, hq⟩ := hpF
  have hqh : q.IsHomogeneous d := by
    apply MvPolynomial.IsHomogeneous.of_map f.injective
    rwa [hq]
  obtain ⟨x, hx, hqx⟩ := isC1_finite_ratFunc K F n d q hd hdn hqh
  refine ⟨f ∘ x, ?_, ?_⟩
  · intro hz
    apply hx
    funext i
    apply f.injective
    simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hz i
  · have h := congrArg f hqx
    rwa [MvPolynomial.map_eval, hq, map_zero] at h

end Field
