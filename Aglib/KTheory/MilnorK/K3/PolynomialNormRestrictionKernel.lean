/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialNorm
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# The finite separable restriction kernel is killed by the degree

One primitive-element presentation supplies an auxiliary linear map whose
composite with restriction is the actual field degree. No canonical norm,
presentation independence, or norm tower is asserted or needed.
-/

@[expose] public noncomputable section

namespace MilnorK.K2

open Polynomial MilnorK.K3.PolynomialNorm MilnorK.K3.PolynomialResidue

variable (k E : Type*) [Field k] [Field E] [Algebra k E]
  [FiniteDimensional k E] [Algebra.IsSeparable k E]

/-- One polynomial presentation gives a degree retraction of the original
restriction map. The existential map is not asserted to be a canonical norm. -/
theorem exists_degree_retraction :
    ∃ T : MilnorK.K2.Group E →ₗ[ℤ] MilnorK.K2.Group k,
      ∀ x : MilnorK.K2.Group k, T (map (algebraMap k E) x) = (Module.finrank k E : ℤ) • x := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element k E
  let p : MonicIrreducible k :=
    ⟨minpoly k a, minpoly.monic (IsIntegral.of_finite k a),
      minpoly.irreducible (IsIntegral.of_finite k a)⟩
  let : Fact (Irreducible p.val) := ⟨p.property.2⟩
  let e : AdjoinRoot p.val ≃ₐ[k] E :=
    (IntermediateField.adjoinRootEquivAdjoin k (IsIntegral.of_finite k a)).trans
      ((IntermediateField.equivOfEq ha).trans IntermediateField.topEquiv)
  have hp : p.val.natDegree = Module.finrank k E :=
    (Field.primitive_element_iff_minpoly_natDegree_eq k a).mp ha
  refine ⟨(polynomialNorm p).comp (map e.symm.toRingHom), ?_⟩
  intro x
  have hc : e.symm.toRingHom.comp (algebraMap k E) =
      algebraMap k (AdjoinRoot p.val) := by
    ext c
    exact e.symm.commutes c
  rw [LinearMap.comp_apply, ← LinearMap.comp_apply (map e.symm.toRingHom),
    ← map_comp, hc, polynomialNorm_map_constants, hp]

/-- The actual finite separable degree annihilates every element killed by
restriction. This does not assert that restriction is injective. -/
theorem finrank_smul_eq_zero_of_map_eq_zero (x : MilnorK.K2.Group k)
    (hx : map (algebraMap k E) x = 0) : (Module.finrank k E : ℤ) • x = 0 := by
  obtain ⟨T, hT⟩ := exists_degree_retraction k E
  rw [← hT x, hx, map_zero]

/-- A bound on restricted torsion pulls back with the actual extension degree. -/
theorem mul_finrank_smul_eq_zero_of_smul_map_eq_zero (n : ℤ) (x : MilnorK.K2.Group k)
    (hx : n • map (algebraMap k E) x = 0) :
    (n * (Module.finrank k E : ℤ)) • x = 0 := by
  have h := finrank_smul_eq_zero_of_map_eq_zero k E (n • x) (by rwa [map_smul])
  simpa only [smul_smul, mul_comm] using h

end MilnorK.K2
