/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestrictionExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Open
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Acyclic

/-! # Exact coefficient restriction and the original bounded-below lower shriek

Only exact functors are derived here. No preservation of injective objects by
restriction of scalars, flatness, torsion exponent, or base inversion is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wUΓ wXΓ wUΛ wXΛ

namespace Coefficients

/-- The installed bounded-below functor of the actual exact scalar restriction. -/
abbrev moduleDerivedRestrictScalars (X : Scheme.{u})
    {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)
    [HasDerivedCategory.{wXΓ} (ModuleSheaf X Γ)]
    [HasDerivedCategory.{wXΛ} (ModuleSheaf X Λ)] :
    DerivedCategory.Plus (ModuleSheaf X Γ) ⥤ DerivedCategory.Plus (ModuleSheaf X Λ) :=
  (moduleRestrictScalars X φ).rightDerivedFunctorPlus

end Coefficients

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)
  [HasDerivedCategory.{wUΓ} (ModuleSheaf U Γ)]
  [HasDerivedCategory.{wXΓ} (ModuleSheaf X Γ)]
  [HasDerivedCategory.{wUΛ} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wXΛ} (ModuleSheaf X Λ)]

/-- Derive the existing genuine lower-shriek scalar comparison, without replacing its map. -/
def moduleDerivedLowerShriekScalarRestrictionIso :
    moduleDerivedLowerShriek j Γ ⋙ moduleDerivedRestrictScalars X φ ≅
      moduleDerivedRestrictScalars U φ ⋙ moduleDerivedLowerShriek j Λ :=
  (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
      (moduleLowerShriek j Γ) (moduleRestrictScalars X φ)).symm ≪≫
    (moduleLowerShriek j Γ ⋙ moduleRestrictScalars X φ).rightDerivedFunctorPlusIso
      (moduleLowerShriekScalarRestrictionIso j φ) ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
      (moduleRestrictScalars U φ) (moduleLowerShriek j Λ)

/-- The comparison retains the original composite derived units and the original complex map. -/
@[reassoc]
theorem moduleDerivedLowerShriekScalarRestrictionIso_unit
    (K : CochainComplex.Plus (ModuleSheaf U Γ)) :
    (Functor.rightDerivedFunctorPlusCompUnit (moduleLowerShriek j Γ)
        (moduleRestrictScalars X φ)).app K ≫
      (moduleDerivedLowerShriekScalarRestrictionIso j φ).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (moduleLowerShriekScalarRestrictionIso j φ)).hom.app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit
        (moduleRestrictScalars U φ) (moduleLowerShriek j Λ)).app K := by
  rw [Functor.rightDerivedFunctorPlusCompUnit_app,
    ← Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app]
  simp only [moduleDerivedLowerShriekScalarRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, Functor.rightDerivedFunctorPlusIso_hom_app, Category.assoc,
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app,
    Functor.rightDerivedFunctorPlusCompUnit_app]

end AlgebraicGeometry.Scheme.EtaleCohomology
