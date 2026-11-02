/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.GenericConnectedness
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Clopens of the original smooth affine generic fibre lift

The actual generic tensor algebra has no new idempotents over the supplied
integrally closed base and fraction field. The native tensor-spectrum
comparison carries this fact to the original scheme pullback, with the exact
original projection preimage equation. No Noetherian or connected-source
hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- Lift a clopen of the original smooth affine generic fibre to the original
affine scheme, retaining literal preimage under the original projection. -/
theorem exists_clopen_generic_preimage_of_smooth_algebra
    (R K B : Type u) [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (U : (pullback (Spec.algebraMap R B) (Spec.algebraMap R K)).Opens)
    (hU : IsClosed (U : Set (pullback (Spec.algebraMap R B)
      (Spec.algebraMap R K) : Scheme.{u}))) :
    ∃ V : (Spec (.of B)).Opens, IsClosed (V : Set (Spec (.of B))) ∧
      pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R K) ⁻¹ᵁ V = U := by
  let e := pullbackSpecIso R B K
  have hcl : IsClopen (e.inv ⁻¹' (U : Set (pullback (Spec.algebraMap R B)
      (Spec.algebraMap R K) : Scheme.{u}))) :=
    ⟨hU.preimage e.inv.continuous, U.isOpen.preimage e.inv.continuous⟩
  obtain ⟨z, hz, heU⟩ := PrimeSpectrum.isClopen_iff.mp hcl
  obtain ⟨a, ha, haz⟩ := Algebra.Smooth.generic_idempotent_lifts R K B z hz
  let V : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen a
  have hV : IsClosed (V : Set (Spec (.of B))) :=
    (PrimeSpectrum.isClopen_iff.mpr ⟨a, ha, rfl⟩).1
  have heq : e.inv ⁻¹ᵁ
      (pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R K) ⁻¹ᵁ V) =
      e.inv ⁻¹ᵁ U := by
    change (pullbackSpecIso R B K).inv ⁻¹ᵁ
      (pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R K) ⁻¹ᵁ V) = _
    rw [← Hom.comp_preimage, pullbackSpecIso_inv_fst']
    change PrimeSpectrum.basicOpen (algebraMap B (B ⊗[R] K) a) = e.inv ⁻¹ᵁ U
    rw [haz]
    exact TopologicalSpace.Opens.ext heU.symm
  have hfinal := congrArg (fun W => e.hom ⁻¹ᵁ W) heq
  refine ⟨V, hV, ?_⟩
  simpa only [← Hom.comp_preimage, Iso.hom_inv_id, Iso.hom_inv_id_assoc,
    Hom.id_preimage] using hfinal

end AlgebraicGeometry.Scheme
