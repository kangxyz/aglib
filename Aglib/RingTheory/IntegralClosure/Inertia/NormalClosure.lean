/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteEtale.CoefficientInertia
public import Aglib.RingTheory.IntegralClosure.Inertia.Etale

/-!
# Etaleness of normalized normal closures over a DVR

The actual finite-etale model fixes every generic embedding under inertia.
Consequently its normal closure is fixed, and the arbitrary-residue inertia
criterion proves etaleness of its literal normalization. The specified generic
fiber equivalence is retained. No residue perfectness or group-order division
is used, and no global purity assertion is made.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace integralClosure.Inertia

variable (R K Ω H E : Type*) [CommRing R] [Field K] [Algebra R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [CommRing H] [Algebra R H] [Module.Finite R H] [Algebra.Etale R H]
  [Field E] [Algebra K E]

/-- Inertia fixes every embedding of the specified generic field, not merely
one chosen embedding of the finite-etale model. -/
theorem all_embeddings_fixed_of_finiteEtaleModel
    (e : (K ⊗[R] H) ≃ₐ[K] E)
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ Q.inertia (Ω ≃ₐ[K] Ω))
    (f : E →ₐ[K] Ω) : σ.toAlgHom.comp f = f := by
  have h := Algebra.FiniteEtale.CoefficientInertia.coefficients_fixed_by_absolute_inertia
    R K Ω H Q σ hσ (f.comp e.toAlgHom)
  ext x
  obtain ⟨z, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun h z

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
  [IsGalois K Ω] [FiniteDimensional K E]

/-- A finite-etale model of a finite field extension over a DVR gives an etale
normalization of its actual normal closure inside the specified Galois field. -/
theorem normalClosure_etale_of_finiteEtaleModel
    (e : (K ⊗[R] H) ≃ₐ[K] E)
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    Algebra.Etale R (integralClosure R (IntermediateField.normalClosure K E Ω)) := by
  let N : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := IntermediateField.normalClosure K E Ω }
  have hle := HorizontalNonGalois.normalClosure_le_fixedField_of_trivial_on_generic_fiber
    R K Ω E Q (all_embeddings_fixed_of_finiteEtaleModel R K Ω H E e Q)
  exact Absolute.model_etale_of_absolute_inertia_fixed R K Ω Q N
    (fun σ hσ x => (IntermediateField.mem_fixedField_iff _ _).mp (hle x.property) σ hσ)

end integralClosure.Inertia
