/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.ClopenSections
public import Aglib.AlgebraicGeometry.Spec.AdicSectionRetraction

/-! # Original clopen extension from bijective scalar sections

A clopen subset extends using its actual idempotent global section and the
inverse of the original scalar map. The extended subset is a literal basic
open of the original affine target, with its exact inverse-image equation.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- Bijective original scalar sections extend every clopen open to an
idempotent basic open of the same affine target. -/
theorem exists_idempotent_basicOpen_preimage_eq_of_affineScalar_bijective
    {C : Type u} [CommRing C] {X : Scheme.{u}} (f : X ⟶ Spec (.of C))
    (hf : Function.Bijective (affineScalarMap f))
    (U : X.Opens) (hU : IsClosed (U : Set X)) :
    ∃ e : C, IsIdempotentElem e ∧
      f ⁻¹ᵁ (PrimeSpectrum.basicOpen e) = U := by
  obtain ⟨s, hs, hbasic⟩ := exists_idempotent_basicOpen_eq X U hU
  obtain ⟨e, he⟩ := hf.surjective s
  refine ⟨e, ?_, ?_⟩
  · apply hf.injective
    rw [map_mul, he]
    exact hs
  · have hb : (Spec (.of C)).basicOpen ((ΓSpecIso (.of C)).inv e) =
        (PrimeSpectrum.basicOpen e : (Spec (.of C)).Opens) :=
      basicOpen_eq_of_affine (R := CommRingCat.of C) e
    rw [← hb, Scheme.preimage_basicOpen_top]
    change X.basicOpen (affineScalarMap f e) = U
    rw [he, hbasic]

/-- The extended basic open is clopen in the original affine target. -/
theorem exists_clopen_preimage_eq_of_affineScalar_bijective
    {C : Type u} [CommRing C] {X : Scheme.{u}} (f : X ⟶ Spec (.of C))
    (hf : Function.Bijective (affineScalarMap f))
    (U : X.Opens) (hU : IsClosed (U : Set X)) :
    ∃ V : (Spec (.of C)).Opens, IsClosed (V : Set (Spec (.of C))) ∧ f ⁻¹ᵁ V = U := by
  obtain ⟨e, he, h⟩ :=
    exists_idempotent_basicOpen_preimage_eq_of_affineScalar_bijective f hf U hU
  exact ⟨PrimeSpectrum.basicOpen e, (PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩).isClosed, h⟩

end AlgebraicGeometry.Scheme
