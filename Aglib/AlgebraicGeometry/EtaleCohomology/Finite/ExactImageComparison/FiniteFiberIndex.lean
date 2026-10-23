/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.FiniteLocalFactors
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Embedding the actual finite local residue fields into a common geometric field

Finite local residue extensions over a separably closed residue field can be
nontrivially purely inseparable. Their embedding in the chosen algebraically
closed geometric field is nevertheless unique. No equality of residue fields
is used here.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u v w

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)]
  (C : Type v) [CommRing C] [IsLocalRing C] [Algebra R C] [Module.Finite R C]
  [IsLocalHom (algebraMap R C)]
  (Ω : Type w) [Field Ω] [IsAlgClosed Ω] [Algebra (ResidueField R) Ω]

/-- The actual finite local residue field has a unique embedding into the common
geometric field, over the actual base residue field. -/
def finiteLocalResidueEmbedding : ResidueField C →ₐ[ResidueField R] Ω :=
  IsAlgClosed.lift

/-- Uniqueness follows from pure inseparability, not from identifying either field. -/
theorem finiteLocalResidueEmbedding_unique (a : ResidueField C →ₐ[ResidueField R] Ω) :
    a = finiteLocalResidueEmbedding R C Ω := by
  let : IsPurelyInseparable (ResidueField R) (ResidueField C) :=
    HenselianLocalRing.residueField_isPurelyInseparable_of_finite_local_algebra R C
  exact Subsingleton.elim _ _

/-- The embedding retains the original base residue map on every actual base element. -/
@[simp]
theorem finiteLocalResidueEmbedding_residue_algebraMap (r : R) :
    finiteLocalResidueEmbedding R C Ω (residue C (algebraMap R C r)) =
      algebraMap (ResidueField R) Ω (residue R r) := by
  rw [← ResidueField.algebraMap_residue]
  exact (finiteLocalResidueEmbedding R C Ω).commutes (residue R r)

/-- The exact ring-map triangle used when turning this embedding into a geometric point. -/
theorem finiteLocalResidueEmbedding_comp_residue :
    ((finiteLocalResidueEmbedding R C Ω).toRingHom.comp (residue C)).comp (algebraMap R C) =
      (algebraMap (ResidueField R) Ω).comp (residue R) := by
  ext r
  exact finiteLocalResidueEmbedding_residue_algebraMap R C Ω r

end AlgebraicGeometry.Scheme.EtaleCohomology
