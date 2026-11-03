/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.Topology.Separation.Basic

/-! # A closed boundary point of an affine curve compactification

A whole affine curve of dimension one cannot be proper over a field: a proper
morphism between affine schemes is finite, whereas finite morphisms do not
increase dimension. Compactness produces a closed point of the actual boundary.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- The original open immersion omits a closed point; no rationality of that
point and no smoothness or normality of the compactification are needed. -/
theorem exists_closedPoint_outside_affine_curve_compactification
    (k : Type u) [Field k] {U X : Scheme.{u}} [IsAffine U]
    (p : U ⟶ Spec (.of k)) (r : X ⟶ Spec (.of k)) [IsProper r]
    (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ r = p)
    (hdim : topologicalKrullDim U = 1) :
    ∃ x : X, IsClosed ({x} : Set X) ∧ x ∉ Set.range j := by
  have hboundary : ∃ x : X, x ∉ Set.range j := by
    by_contra! hsurj
    let : Surjective j := ⟨hsurj⟩
    let : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr
      ⟨inferInstance, inferInstance⟩
    let : IsProper p := by rw [← h]; infer_instance
    let : IsFinite p := IsFinite.iff_isProper_and_isAffineHom.mpr
      ⟨inferInstance, inferInstance⟩
    have hle := p.topologicalKrullDim_le_of_isFinite
    have hz : topologicalKrullDim (Spec (.of k)) = 0 := by
      change topologicalKrullDim (PrimeSpectrum k) = 0
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
    rw [hdim, hz] at hle
    exact (by norm_num : ¬ (1 : WithBot ℕ∞) ≤ 0) hle
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace r
  have hc : IsClosed ((Set.range j)ᶜ : Set X) := j.opensRange.isOpen.isClosed_compl
  obtain ⟨x, hx, hclosed⟩ := hc.exists_closed_singleton hboundary
  exact ⟨x, hclosed, hx⟩

end AlgebraicGeometry.Scheme
