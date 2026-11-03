/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FiniteType
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Affine
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction


/-!
# AlgebraicGeometry / Modules / Differentials / Relative / ExteriorAffine

Source: `IntegralTrace/AffineForms.lean`.
Incoming SHA256: `ea11236c4f28ac7e3ee837ae044c406f72d7e17b25e0cd53ada761d5e6f8034f`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X : Scheme.{u}} {Λ R : CommRingCat.{u}}
  (a : X ⟶ Spec Λ) (j : Spec R ⟶ X) [IsOpenImmersion j] (n : ℕ)

/-- Original raw forms on the affine chart are the tilde of the actual exterior module. -/
def rawFormsAffineChartIso :
    (moduleExteriorPower X (relativeDifferentialSheaf a) n).restrict j ≅
      tilde (ModuleCat.of R
        (⋀[R]^n (CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ a))))) :=
  (moduleExteriorPowerRestrictionIso j (relativeDifferentialSheaf a) n).symm ≪≫
    (moduleExteriorPowerFunctor (Spec R) n).mapIso (relativeDifferentialAffineChartIso a j) ≪≫
      exteriorTildeIso (CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ a))) n
/-- Actual affine sections of raw forms, with the original coefficient algebra. -/
def rawFormsAffineSectionsEquiv :
    moduleSpecΓFunctor.obj ((moduleExteriorPower X (relativeDifferentialSheaf a) n).restrict j)
      ≃ₗ[R] ⋀[R]^n (CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ a))) :=
  ((moduleSpecΓFunctor.mapIso (rawFormsAffineChartIso a j n)) ≪≫
    (tilde.toTildeΓNatIso.app (ModuleCat.of R
      (⋀[R]^n (CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ a)))))).symm).toLinearEquiv

end AlgebraicGeometry.Scheme.Modules.Differentials
