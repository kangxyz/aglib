/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ResidueFiber

/-! Actual coefficient and residue pullback triangles, and unconditional domain integrality. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace WeierstrassBaseChangeTest

variable {R S : Type u} [CommRing R] [CommRing S]

example (W : WeierstrassCurve R) (f : R →+* S) :
    WeierstrassCurve.Projective.coefficientSchemeMap W f ≫
      WeierstrassCurve.Projective.structureMap W =
    WeierstrassCurve.Projective.structureMap (W.map f) ≫ Spec.map (CommRingCat.ofHom f) :=
  WeierstrassCurve.Projective.coefficientSchemeMap_structure W f

example [Algebra R S] (W : WeierstrassCurve R) :
    (WeierstrassCurve.Projective.coefficientBaseChangeIso (S := S) W).hom ≫
      pullback.fst _ _ =
        WeierstrassCurve.Projective.coefficientSchemeMap W (algebraMap R S) :=
  WeierstrassCurve.Projective.coefficientBaseChangeIso_hom_fst W

example [IsDomain R] (W : WeierstrassCurve R) :
    IsIntegral (WeierstrassCurve.Projective.scheme W) :=
  WeierstrassCurve.Projective.scheme_isIntegral_of_isDomain W

example [IsLocalRing R] (W : WeierstrassCurve R) :
    WeierstrassCurve.Projective.specialFibre W =
      Scheme.LocalRing.ResidueFiber.obj (WeierstrassCurve.Projective.structureMap W) := rfl

example [IsLocalRing R] (W : WeierstrassCurve R) :
    IsIntegral (Scheme.LocalRing.ResidueFiber.obj (WeierstrassCurve.Projective.structureMap W)) :=
  WeierstrassCurve.Projective.specialFibre_isIntegral W

example [IsLocalRing R] (W : WeierstrassCurve R) :
    (WeierstrassCurve.Projective.specialCoefficientIso W).hom ≫ pullback.fst _ _ =
      WeierstrassCurve.Projective.coefficientSchemeMap W (IsLocalRing.residue R) :=
  WeierstrassCurve.Projective.specialCoefficientIso_hom_fst W

end WeierstrassBaseChangeTest
