/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.SeparablyClosedResidue

/-! # The residue field at a rational geometric neighborhood system

A surjective base point identifies the actual residue field of the geometric
neighborhood colimit with the chosen field. In particular this applies to a
split rational point. No separable-closedness hypothesis is necessary.
-/

@[expose] public noncomputable section

universe u

namespace GeometricEtaleColimit

variable (R k : Type u) [CommRing R] [Field k] [Algebra R k]

/-- A surjective base point makes the actual colimit point surjective. -/
theorem residue_surjective_of_surjective (h : Function.Surjective (algebraMap R k)) :
    Function.Surjective (residue R k) := by
  intro x
  obtain ⟨r, rfl⟩ := h x
  exact ⟨algebraMap R (GeometricEtaleColimit R k) r, (residue R k).commutes r⟩

/-- At a rational base point the canonical residue-field embedding is onto. -/
theorem residueFieldEmbedding_surjective (h : Function.Surjective (algebraMap R k)) :
    Function.Surjective (residueFieldEmbedding R k) := by
  intro x
  obtain ⟨r, hr⟩ := residue_surjective_of_surjective R k h x
  refine ⟨IsLocalRing.residue (GeometricEtaleColimit R k) r, ?_⟩
  exact (RingHom.congr_fun (residueFieldEmbedding_comp_residue R k) r).trans hr

/-- The canonical residue-field equivalence, with the original embedding as forward map. -/
def rationalResidueEquiv (h : Function.Surjective (algebraMap R k)) :
    IsLocalRing.ResidueField (GeometricEtaleColimit R k) ≃+* k :=
  RingEquiv.ofBijective (residueFieldEmbedding R k)
    ⟨(residueFieldEmbedding R k).injective, residueFieldEmbedding_surjective R k h⟩

theorem rationalResidueEquiv_toRingHom (h : Function.Surjective (algebraMap R k)) :
    (rationalResidueEquiv R k h).toRingHom = residueFieldEmbedding R k := rfl

/-- The inverse equivalence retains the literal colimit-to-residue map. -/
theorem rationalResidueEquiv_symm_comp_residue
    (h : Function.Surjective (algebraMap R k)) :
    (rationalResidueEquiv R k h).symm.toRingHom.comp (residue R k).toRingHom =
      IsLocalRing.residue (GeometricEtaleColimit R k) := by
  ext x
  apply (rationalResidueEquiv R k h).injective
  exact ((rationalResidueEquiv R k h).apply_symm_apply _).trans
    (RingHom.congr_fun (residueFieldEmbedding_comp_residue R k) x).symm

end GeometricEtaleColimit
