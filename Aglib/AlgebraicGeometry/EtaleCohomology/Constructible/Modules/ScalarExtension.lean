/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Basic
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Aglib.CategoryTheory.Sites.Pullback.SheafifiedLeftAdjointCoefficients

/-! # Constructibility of original scalar extension

The actual left-factor tensor and original sheafification preserve the same
finite locally closed partitions and etale charts. No finite-ring hypothesis
is needed: native scalar extension preserves finite generation for every map.
The output coefficient universe lies in the original sheaf-value universe.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] {Λ : Type (u + 1)} [CommRing Λ] (φ : R →+* Λ)

/-- The native extension functor followed by the actual sheafification. -/
abbrev scalarExtensionSheaf (X : Scheme.{u}) : ModuleSheaf R X ⥤ ModuleSheaf Λ X :=
  Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.extendScalars.{r, u + 1, u + 1} φ)

/-- The original pullback commutes with actual scalar extension. -/
def scalarExtensionSheafPullbackIso {X S : Scheme.{u}} (f : S ⟶ X) :
    moduleInverseImage R f ⋙ scalarExtensionSheaf φ S ≅
      scalarExtensionSheaf φ X ⋙ moduleInverseImage Λ f :=
  Functor.sheafPullbackSheafifiedLeftAdjointIso (siteBaseChange f)
    X.smallEtaleTopology S.smallEtaleTopology
    (ModuleCat.extendScalars.{r, u + 1, u + 1} φ)
    (ModuleCat.restrictScalars.{u + 1} φ)
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, r, u + 1} φ)

/-- Constant values are extended by the original left-factor tensor. -/
def scalarExtensionSheafConstantIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙
        scalarExtensionSheaf φ X ≅
      ModuleCat.extendScalars.{r, u + 1, u + 1} φ ⋙
        constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  constantSheafSheafifiedLeftAdjointIso X.smallEtaleTopology
    (ModuleCat.extendScalars.{r, u + 1, u + 1} φ)
    (ModuleCat.restrictScalars.{u + 1} φ)
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, r, u + 1} φ)

/-- The given chart cover is unchanged and every original finite module is extended. -/
def FiniteTypeLocalTrivialization.scalarExtension {X : Scheme.{u}}
    {F : ModuleSheaf R X} (t : FiniteTypeLocalTrivialization F) :
    FiniteTypeLocalTrivialization ((scalarExtensionSheaf φ X).obj F) where
  index := t.index
  chart := t.chart
  covers := t.covers
  value i := (ModuleCat.extendScalars.{r, u + 1, u + 1} φ).obj (t.value i)
  finite_value i := by
    let := t.finite_value i
    exact ModuleCat.finite_extendScalars φ (t.value i)
  trivialization i :=
    ((scalarExtensionSheafPullbackIso φ (t.chart i).hom).app F).symm ≪≫
      (scalarExtensionSheaf φ (t.chart i).left).mapIso (t.trivialization i) ≪≫
      (scalarExtensionSheafConstantIso φ (t.chart i).left).app (t.value i)

/-- Scalar extension preserves finite-type local constancy. -/
theorem isFiniteTypeLocallyConstant_scalarExtension {X : Scheme.{u}}
    {F : ModuleSheaf R X} (hF : IsFiniteTypeLocallyConstant F) :
    IsFiniteTypeLocallyConstant ((scalarExtensionSheaf φ X).obj F) := by
  obtain ⟨t⟩ := hF
  exact ⟨t.scalarExtension φ⟩

/-- Extend only the values on the existing original finite partition. -/
def ConstructiblePartition.scalarExtension {X : Scheme.{u}}
    {F : ModuleSheaf R X} (t : ConstructiblePartition F) :
    ConstructiblePartition ((scalarExtensionSheaf φ X).obj F) where
  toFiniteLocallyClosedPartition := t.toFiniteLocallyClosedPartition
  locally_constant i :=
    (isFiniteTypeLocallyConstant_iff_of_iso
      ((scalarExtensionSheafPullbackIso φ (t.inclusion i)).app F)).mp
        (isFiniteTypeLocallyConstant_scalarExtension φ (t.locally_constant i))

/-- Finite-type constructibility survives arbitrary scalar extension. -/
theorem isConstructible_scalarExtension {X : Scheme.{u}}
    {F : ModuleSheaf R X} (hF : IsConstructible F) :
    IsConstructible ((scalarExtensionSheaf φ X).obj F) := by
  intro U
  obtain ⟨t⟩ := hF U
  exact ⟨(t.scalarExtension φ).ofIso
    ((scalarExtensionSheafPullbackIso φ U.1.ι).app F)⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
