/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestrictionValuedUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestrictionEtale

/-! # Scalar restriction retains the original module-valued lower-shriek adjunction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)

/-- The inverse of the original chart comparison retains the same scalar square. -/
@[reassoc]
theorem moduleValuedInverseImageEtaleIso_inv_scalar (N : ModuleValuedSheaf X Γ) :
    (moduleValuedRestrictScalars U φ).map ((moduleValuedInverseImageEtaleIso j Γ).inv.app N) ≫
      (moduleValuedInverseImageScalarRestrictionIso j φ).hom.app N =
    (moduleValuedInverseImageEtaleIso j Λ).inv.app
      ((moduleValuedRestrictScalars X φ).obj N) := by
  apply (cancel_mono ((moduleValuedInverseImageEtaleIso j Λ).hom.app
    ((moduleValuedRestrictScalars X φ).obj N))).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (moduleValuedRestrictScalars U φ).map
      ((moduleValuedInverseImageEtaleIso j Γ).inv.app N) ≫ k)
        (moduleValuedInverseImageEtaleIso_scalar j φ N).symm).trans
      (((moduleValuedRestrictScalars U φ).mapIso
        ((moduleValuedInverseImageEtaleIso j Γ).app N)).inv_hom_id.trans
          (((moduleValuedInverseImageEtaleIso j Λ).app
            ((moduleValuedRestrictScalars X φ).obj N)).inv_hom_id.symm)))

/-- The original lower-shriek scalar comparison preserves the actual site inverse-image unit. -/
@[reassoc]
theorem moduleValuedLowerShriekScalarRestrictionIso_unit (M : ModuleValuedSheaf U Γ) :
    (moduleValuedRestrictScalars U φ).map ((moduleValuedLowerShriekAdjunction j Γ).unit.app M) ≫
      (moduleValuedInverseImageScalarRestrictionIso j φ).hom.app
        ((moduleValuedLowerShriek j Γ).obj M) ≫
      (moduleValuedInverseImage j Λ).map
        ((moduleValuedLowerShriekScalarRestrictionIso j φ).hom.app M) =
    (moduleValuedLowerShriekAdjunction j Λ).unit.app
      ((moduleValuedRestrictScalars U φ).obj M) := by
  change (moduleValuedRestrictScalars U φ).map
      ((moduleValuedLowerShriekRestrictionAdjunction j Γ).unit.app M ≫
        (moduleValuedInverseImageEtaleIso j Γ).inv.app ((moduleValuedLowerShriek j Γ).obj M)) ≫
      (moduleValuedInverseImageScalarRestrictionIso j φ).hom.app
        ((moduleValuedLowerShriek j Γ).obj M) ≫
      (moduleValuedInverseImage j Λ).map
        ((moduleValuedLowerShriekScalarRestrictionIso j φ).hom.app M) =
    (moduleValuedLowerShriekRestrictionAdjunction j Λ).unit.app
      ((moduleValuedRestrictScalars U φ).obj M) ≫
      (moduleValuedInverseImageEtaleIso j Λ).inv.app
        ((moduleValuedLowerShriek j Λ).obj ((moduleValuedRestrictScalars U φ).obj M))
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (moduleValuedInverseImageEtaleIso_inv_scalar j φ
    ((moduleValuedLowerShriek j Γ).obj M))]
  have hn := (moduleValuedInverseImageEtaleIso j Λ).inv.naturality
    ((moduleValuedLowerShriekScalarRestrictionIso j φ).hom.app M)
  exact (congrArg (fun k => (moduleValuedRestrictScalars U φ).map
    ((moduleValuedLowerShriekRestrictionAdjunction j Γ).unit.app M) ≫ k) hn.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ (moduleValuedInverseImageEtaleIso j Λ).inv.app
          ((moduleValuedLowerShriek j Λ).obj ((moduleValuedRestrictScalars U φ).obj M)))
            (moduleValuedLowerShriekRestriction_scalar_unit j φ M)))

/-- The existing module-valued lower-shriek scalar comparison and existing inverse-image
scalar comparison are the actual adjunction mates. -/
theorem mate_moduleValuedLowerShriekScalarRestrictionIso_inv :
    (mateEquiv (moduleValuedLowerShriekAdjunction j Γ) (moduleValuedLowerShriekAdjunction j Λ)
      (TwoSquare.mk _ _ _ _ (moduleValuedLowerShriekScalarRestrictionIso j φ).inv)).natTrans =
    (moduleValuedInverseImageScalarRestrictionIso j φ).hom :=
  mateEquiv_inv_natTrans_eq_of_unit _ _ _ _
    (moduleValuedLowerShriekScalarRestrictionIso_unit j φ)

end AlgebraicGeometry.Scheme.EtaleCohomology
