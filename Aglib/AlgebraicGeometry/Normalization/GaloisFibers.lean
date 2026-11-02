/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.AffineMap
public import Aglib.AlgebraicGeometry.Spec.GaloisFibers
public import Aglib.AlgebraicGeometry.Morphisms.Etale.AtIso

/-! # Transitivity on fibres of the original Galois normalization

The canonical integral closure is used only through the existing affine
comparison with the supplied normalization. All output points, automorphisms,
and etale neighborhoods belong to that original normalization.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable (R K L : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [IsGalois K L]
  {X : Scheme.{u}} (q : X ⟶ Spec (.of R)) [QuasiCompact q] [QuasiSeparated q]
  (c : Spec (.of L) ≅ X) (hc : c.hom ≫ q = Spec.algebraMap R L)

include R K L c hc

/-- Every two original normalization points over the same base point are
related by an actual automorphism over that base. -/
theorem normalization_exists_iso_over_eq_of_image_eq
    (x y : q.normalization) (h : q.fromNormalization x = q.fromNormalization y) :
    ∃ e : q.normalization ≅ q.normalization,
      e.hom ≫ q.fromNormalization = q.fromNormalization ∧ e.hom x = y := by
  let : IsFractionRing (integralClosure R L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L _
  let : IsGaloisGroup (L ≃ₐ[K] L) R (integralClosure R L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) R (integralClosure R L) K L
  exact Spec.exists_iso_over_eq_of_affine_image_eq R (integralClosure R L) (L ≃ₐ[K] L)
    q.fromNormalization (integralClosureSourceIso R L q c hc)
    (integralClosureSourceIso_hom_over R L q c hc) x y h

/-- Etaleness at one original point propagates to every point of its fibre. -/
theorem normalization_etaleAt_of_image_eq
    (x y : q.normalization) (h : q.fromNormalization x = q.fromNormalization y)
    (hx : q.fromNormalization.etaleAt x) : q.fromNormalization.etaleAt y := by
  obtain ⟨e, he, hp⟩ := normalization_exists_iso_over_eq_of_image_eq R K L q c hc x y h
  simpa only [hp] using hx.map_over_iso e he

end AlgebraicGeometry.Scheme.Hom
