/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.FunctionField.ResidueField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension

/-! # Actual affine coordinates for residue fields on a finite-type curve

The chart and residue-field isomorphism are the native open immersion and its
native residue map. The source scheme may be nonreduced or reducible; no point
is replaced by a reduced component of the whole scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k))
  [LocallyOfFiniteType p]

/-- Every actual point has a finite-type affine chart of dimension at most one,
whose actual prime residue field is canonically isomorphic to the original residue field. -/
theorem exists_curve_residueField_coordinates (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X) (y : Spec R),
      IsOpenImmersion f ∧ f y = x ∧
      (Spec.preimage (f ≫ p)).hom.FiniteType ∧ ringKrullDim R ≤ 1 ∧
      Nonempty (X.residueField x ≃+* y.asIdeal.ResidueField) := by
  obtain ⟨R, f, hf, y, hxy⟩ := Scheme.exists_Spec_apply_eq x
  let : IsOpenImmersion f := hf
  have hxy' : f y = x := hxy
  subst x
  refine ⟨R, f, y, hf, rfl, ?_, ?_, ?_⟩
  · apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  · calc
      ringKrullDim R = topologicalKrullDim (Spec R) :=
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R).symm
      _ ≤ topologicalKrullDim X :=
        f.isOpenEmbedding.isInducing.topologicalKrullDim_le
      _ ≤ 1 := hdim
  · exact ⟨(asIso (f.residueFieldMap y) ≪≫
      Spec.residueFieldIso R y).commRingCatIsoToRingEquiv⟩

end AlgebraicGeometry.Scheme
