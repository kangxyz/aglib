/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.ScalarRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Actual scalar restriction along a map of constant coefficient rings -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

attribute [local instance] hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard

attribute [local instance] CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard


variable (X : Scheme.{u}) {Λ Γ : Type (u + 1)} [Ring Λ] [Ring Γ] (φ : Λ →+* Γ)

/-- The actual constant ring sheaf map induced by the given ring homomorphism. -/
def constantRingCoefficientMap : constantRing X Λ ⟶ constantRing X Γ :=
  ModuleCat.Sheaf.ConstantRing.constantRingCoefficientMap.{
    u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) φ

/-- The ring coefficient map retains the original constant-sheaf units. -/
@[reassoc]
theorem constantRingCoefficientMap_unit :
    constantRingUnit X Λ ≫ (constantRingCoefficientMap X φ).hom =
      (Functor.const X.Etaleᵒᵖ).map (RingCat.ofHom φ) ≫ constantRingUnit X Γ :=
  ModuleCat.Sheaf.ConstantRing.constantRingCoefficientMap_unit.{
    u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) φ

/-- Restriction along the actual map of sheaves of constant rings. -/
def moduleRestrictScalars : ModuleSheaf X Γ ⥤ ModuleSheaf X Λ :=
  ModuleCat.Sheaf.ConstantRing.moduleRestrictScalars.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) φ

/-- Pointwise restriction of scalars on original module-valued sheaves. -/
def moduleValuedRestrictScalars : ModuleValuedSheaf X Γ ⥤ ModuleValuedSheaf X Λ :=
  ModuleCat.Sheaf.ConstantRing.moduleValuedRestrictScalars.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) φ

/-- Sectionwise scalar restriction is the original composition of ring maps. -/
def moduleRestrictScalarsComparisonComponent (M : ModuleSheaf X Γ) (U : X.Etaleᵒᵖ) :
    (((moduleSheafEquivalence X Λ).inverse.obj
      ((moduleRestrictScalars X φ).obj M)).obj.obj U) ≅
    (((moduleValuedRestrictScalars X φ).obj
      ((moduleSheafEquivalence X Γ).inverse.obj M)).obj.obj U) :=
  ModuleCat.Sheaf.ConstantRing.moduleRestrictScalarsComparisonComponent.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) φ M U

/-- Native scalar restriction commutes with the actual inverse coefficient equivalence. -/
def moduleRestrictScalarsComparison :
    moduleRestrictScalars X φ ⋙ (moduleSheafEquivalence X Λ).inverse ≅
      (moduleSheafEquivalence X Γ).inverse ⋙ moduleValuedRestrictScalars X φ :=
  ModuleCat.Sheaf.ConstantRing.moduleRestrictScalarsComparison.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) φ

/-- The native scalar restriction has exactly the transported module-valued realization. -/
def moduleRestrictScalarsTransportIso :
    moduleRestrictScalars X φ ≅
      (moduleSheafEquivalence X Γ).inverse ⋙ moduleValuedRestrictScalars X φ ⋙
        (moduleSheafEquivalence X Λ).functor :=
  ModuleCat.Sheaf.ConstantRing.moduleRestrictScalarsTransportIso.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) φ

/-- Scalar restriction preserves the sheafification class on the actual étale site. -/
theorem moduleRestrictScalars_preservesSheafification :
    (Scheme.smallEtaleTopology X).PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1} φ) :=
  ModuleCat.Sheaf.ConstantRing.moduleRestrictScalars_preservesSheafification.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) φ

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
