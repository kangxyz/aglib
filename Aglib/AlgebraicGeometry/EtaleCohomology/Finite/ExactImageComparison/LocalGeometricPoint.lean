/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteFiberIndex

/-! # The actual geometric point of a finite local component

The chosen residue embedding gives a literal ring map from the finite local
component. Its uniqueness is expressed using the original base ring map,
without identifying the component residue field with the geometric field.
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

/-- The actual ring map defining the geometric point of a finite local component. -/
def finiteLocalGeometricPoint : C →+* Ω :=
  (finiteLocalResidueEmbedding R C Ω).toRingHom.comp (residue C)

/-- The geometric point lies over the original base residue map. -/
theorem finiteLocalGeometricPoint_comp_algebraMap :
    (finiteLocalGeometricPoint R C Ω).comp (algebraMap R C) =
      (algebraMap (ResidueField R) Ω).comp (residue R) :=
  finiteLocalResidueEmbedding_comp_residue R C Ω

/-- Any local map from the component into the same geometric field, lying over
that original base map, is the chosen geometric point. -/
theorem finiteLocalGeometricPoint_unique (a : C →+* Ω) [IsLocalHom a]
    (ha : a.comp (algebraMap R C) =
      (algebraMap (ResidueField R) Ω).comp (residue R)) :
    a = finiteLocalGeometricPoint R C Ω := by
  let b : ResidueField C →ₐ[ResidueField R] Ω :=
    { ResidueField.lift a with
      commutes' := by
        intro x
        obtain ⟨r, rfl⟩ := residue_surjective x
        rw [ResidueField.algebraMap_residue]
        change a (algebraMap R C r) = _
        exact RingHom.congr_fun ha r }
  have hb := finiteLocalResidueEmbedding_unique R C Ω b
  ext c
  have hc := congrArg (fun z : ResidueField C →ₐ[ResidueField R] Ω =>
    z (residue C c)) hb
  exact hc

end AlgebraicGeometry.Scheme.EtaleCohomology
