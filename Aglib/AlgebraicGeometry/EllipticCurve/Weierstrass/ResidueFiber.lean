/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.BaseChange
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Integrality
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber

/-!
# The actual residue fibre of a Weierstrass cubic

The literal local-ring residue pullback is identified with the coefficient
reduction of the same equation. Its integrality follows from the proved
domain theorem for every Weierstrass equation over the residue field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial TensorProduct
universe u v

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- This is the actual special fibre, defined by the fixed structural map and residue map. -/
abbrev specialFibre (W : WeierstrassCurve R) : Scheme.{u} :=
  Scheme.LocalRing.ResidueFiber.obj (structureMap W)

/-- The coefficient equation is the actual special fibre, with no supplied fibre model. -/
def specialCoefficientIso (W : WeierstrassCurve R) :
    scheme (W.baseChange (IsLocalRing.ResidueField R)) ≅ specialFibre W :=
  coefficientBaseChangeIso (S := IsLocalRing.ResidueField R) W

@[reassoc (attr := simp)] theorem specialCoefficientIso_hom_fst (W : WeierstrassCurve R) :
    (specialCoefficientIso W).hom ≫ pullback.fst _ _ =
      coefficientSchemeMap W (IsLocalRing.residue R) :=
  coefficientBaseChangeIso_hom_fst (S := IsLocalRing.ResidueField R) W

@[reassoc (attr := simp)] theorem specialCoefficientIso_hom_snd (W : WeierstrassCurve R) :
    (specialCoefficientIso W).hom ≫ pullback.snd _ _ =
      structureMap (W.baseChange (IsLocalRing.ResidueField R)) :=
  coefficientBaseChangeIso_hom_snd (S := IsLocalRing.ResidueField R) W

/-- Integrality of every actual local-ring special fibre; no assumption on reduced `Δ`. -/
theorem specialFibre_isIntegral (W : WeierstrassCurve R) : IsIntegral (specialFibre W) := by
  let : IsIntegral (scheme (W.baseChange (IsLocalRing.ResidueField R))) :=
    scheme_isIntegral_of_isDomain _
  exact IsIntegral.of_isIso (specialCoefficientIso W).hom
end WeierstrassCurve.Projective

/- Migration source: PointedResolution.Weierstrass.Surface:100–123 only.
Frozen R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 9ece193722de7b23aea25be3cb9ba89193896d67bbc963e574eb18dfd3c0667b.
The shared literal ResidueFiber carrier is reused; no surface or marked model is introduced. -/
