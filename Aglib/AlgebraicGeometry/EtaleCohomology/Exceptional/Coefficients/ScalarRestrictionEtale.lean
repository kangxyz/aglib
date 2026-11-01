/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestrictionAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.EtaleRestriction

/-! # Scalar restriction and the original étale-chart inverse-image comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

private theorem adjunctionComparison_of_unitSquare
    {A B : Type*} [Category* A] [Category* B]
    {F : A ⥤ B} {R : B ⥤ A} (a : F ⊣ R)
    {M : A} {N P : B} (e : N ≅ F.obj M) (u : M ⟶ R.obj N)
    (c : N ⟶ P) (d : F.obj M ⟶ P)
    (hu : u ≫ R.map e.hom = a.unit.app M)
    (hc : u ≫ R.map c = a.unit.app M ≫ R.map d) :
    c = e.hom ≫ d := by
  apply (cancel_epi e.inv).mp
  rw [e.inv_hom_id_assoc]
  apply (a.homEquiv M P).injective
  change a.unit.app M ≫ R.map (e.inv ≫ c) = a.unit.app M ≫ R.map d
  calc
    _ = (u ≫ R.map e.hom) ≫ R.map (e.inv ≫ c) :=
      congrArg (fun z => z ≫ R.map (e.inv ≫ c)) hu.symm
    _ = u ≫ R.map c := by
      rw [R.map_comp, Category.assoc, ← R.map_comp_assoc,
        e.hom_inv_id, R.map_id, Category.id_comp]
    _ = _ := hc

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)

/-- Restriction of scalars retains the literal chart-adjunction unit. -/
theorem moduleValuedEtaleRestrictionAdjunction_scalar_unit (M : ModuleValuedSheaf X Γ) :
    (moduleValuedRestrictScalars X φ).map
      ((moduleValuedEtaleRestrictionAdjunction j Γ).unit.app M) =
    (moduleValuedEtaleRestrictionAdjunction j Λ).unit.app
      ((moduleValuedRestrictScalars X φ).obj M) := rfl

/-- The existing inverse-image-to-chart comparison commutes with scalar restriction,
with its original unit normalization. -/
theorem moduleValuedInverseImageEtaleIso_scalar (M : ModuleValuedSheaf X Γ) :
    (moduleValuedRestrictScalars U φ).map
        ((moduleValuedInverseImageEtaleIso j Γ).hom.app M) =
    (moduleValuedInverseImageScalarRestrictionIso j φ).hom.app M ≫
      (moduleValuedInverseImageEtaleIso j Λ).hom.app
        ((moduleValuedRestrictScalars X φ).obj M) := by
  exact adjunctionComparison_of_unitSquare
    (moduleValuedInverseImageAdjunction j Λ)
    ((moduleValuedInverseImageScalarRestrictionIso j φ).app M)
    ((moduleValuedRestrictScalars X φ).map
      ((moduleValuedInverseImageAdjunction j Γ).unit.app M))
    ((moduleValuedRestrictScalars U φ).map
      ((moduleValuedInverseImageEtaleIso j Γ).hom.app M))
    ((moduleValuedInverseImageEtaleIso j Λ).hom.app
      ((moduleValuedRestrictScalars X φ).obj M))
    (moduleValuedInverseImageScalarRestrictionIso_unit j φ M)
    (((moduleValuedRestrictScalars X φ).map_comp
      ((moduleValuedInverseImageAdjunction j Γ).unit.app M)
      ((moduleValuedDirectImage j Γ).map
        ((moduleValuedInverseImageEtaleIso j Γ).hom.app M))).symm.trans
      ((congrArg (moduleValuedRestrictScalars X φ).map
        (moduleValuedInverseImageEtaleIso_unit j Γ M)).trans
        ((moduleValuedEtaleRestrictionAdjunction_scalar_unit j φ M).trans
          (moduleValuedInverseImageEtaleIso_unit j Λ
            ((moduleValuedRestrictScalars X φ).obj M)).symm)))

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
