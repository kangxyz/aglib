/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.AffineStein
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# A proper quasi-affine scheme over a Noetherian affine base is finite

Proper coherent H⁰ finiteness applies to the original global section ring.
The original affinization is an open immersion by quasi-affineness, and is
proper by the factorization through that finite section ring. Thus both
factors are finite. This includes nonreduced schemes and needs no smoothness,
integrality or dimension hypothesis.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- Properness is retained in the finiteness criterion for a quasi-affine
scheme over a Noetherian affine base. -/
theorem isFinite_of_isProper_of_isQuasiAffine
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.IsQuasiAffine]
    (p : X ⟶ Spec (.of R)) [IsProper p] : IsFinite p := by
  let c : CommRingCat.of R ⟶ Γ(X, ⊤) := (ΓSpecIso (.of R)).inv ≫ p.appTop
  have hc : c.hom.Finite := AffineStein.finite_structuralCoefficients R p
  let : IsFinite (Spec.map c) := (IsFinite.SpecMap_iff c).mpr hc
  have hfac : X.toSpecΓ ≫ Spec.map c = p := by
    dsimp only [c]
    rw [Spec.map_comp, ← toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have : IsProper (X.toSpecΓ ≫ Spec.map c) := by rw [hfac]; infer_instance
  have : IsProper X.toSpecΓ := IsProper.of_comp X.toSpecΓ (Spec.map c)
  have : IsFinite X.toSpecΓ := IsFinite.of_isProper_of_locallyQuasiFinite X.toSpecΓ
  rw [← hfac]
  infer_instance

end AlgebraicGeometry.Scheme
