/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Continuous restriction of scalars

Source: `R5Lab.Aglib.FieldTheory.AbsoluteGaloisGroup.RestrictScalars`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Topology TensorProduct

namespace Field.absoluteGaloisGroup


/-- Restricting scalars on automorphisms is continuous for the actual Krull
topologies in an algebraic tower. -/
theorem restrictScalars_continuous
    (K L Ω : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsAlgebraic L Ω] :
    Continuous (AlgEquiv.restrictScalarsHom K : (Ω ≃ₐ[L] Ω) →* (Ω ≃ₐ[K] Ω)) := by
  classical
  let f := (AlgEquiv.restrictScalarsHom K : (Ω ≃ₐ[L] Ω) →* (Ω ≃ₐ[K] Ω))
  apply continuous_of_continuousAt_one f
  rw [ContinuousAt, map_one]
  refine ((galGroupBasis L Ω).nhds_one_hasBasis.tendsto_iff
    (galGroupBasis K Ω).nhds_one_hasBasis).mpr ?_
  rintro _ ⟨_, ⟨E, hE : FiniteDimensional K E, rfl⟩, rfl⟩
  refine ⟨_, ⟨_, ⟨IntermediateField.adjoin L (E : Set Ω), ?_, rfl⟩, rfl⟩,
    fun σ hσ x => ?_⟩
  · suffices Algebra.EssFiniteType L (IntermediateField.adjoin L (E : Set Ω)) by
      exact Algebra.finite_of_essFiniteType_of_isAlgebraic
    have hfin : Algebra.EssFiniteType K E := inferInstance
    rw [IntermediateField.essFiniteType_iff] at hfin ⊢
    obtain ⟨s, rfl⟩ := hfin
    exact ⟨s, by rw [IntermediateField.adjoin_adjoin_right]⟩
  · exact hσ ⟨(x : Ω), IntermediateField.subset_adjoin L _ x.property⟩

variable (K : Type*) [Field K] [CharZero K]

/-- Actual same-closure restriction of scalars, with the source coefficient group. -/
def closureRestriction (L : IntermediateField K (AlgebraicClosure K)) :
    ((AlgebraicClosure K) ≃ₐ[L] (AlgebraicClosure K)) →* Field.absoluteGaloisGroup K :=
  AlgEquiv.restrictScalarsHom K

end Field.absoluteGaloisGroup
