/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnboundedDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIdentityCoherence
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Original structural comparisons for unbounded module images

Exact inverse-image comparisons are localized with their native factors. The
right-image comparisons are their conjugates under the installed unbounded
adjunctions. Thus their maps retain the original units and counits; no
bounded-below identification or cohomological-dimension hypothesis is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wT
variable (Λ : Type (u + 1)) [Ring Λ]

section Identity
variable (X : Scheme.{u}) [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- Localization of the original exact inverse-image identity. -/
def moduleUnboundedDerivedInverseImageIdIso :
    moduleUnboundedDerivedInverseImage Λ (𝟙 X) ≅ 𝟭 (DerivedCategory (ModuleSheaf X Λ)) :=
  Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ)) _ _ _ _
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (moduleInverseImageIdIso Λ X) (.up ℤ))
        DerivedCategory.Q) ≪≫
    Functor.mapDerivedCategoryIdIso (ModuleSheaf X Λ)

/-- The original unbounded direct-image identity, conjugate to the exact identity. -/
def moduleUnboundedDerivedDirectImageIdIso :
    moduleUnboundedDerivedDirectImage Λ (𝟙 X) ≅ 𝟭 (DerivedCategory (ModuleSheaf X Λ)) :=
  (conjugateIsoEquiv Adjunction.id (moduleUnboundedDerivedAdjunction Λ (𝟙 X))
    (moduleUnboundedDerivedInverseImageIdIso Λ X)).symm

/-- The identity comparison uses precisely the installed original adjunction. -/
theorem conjugateEquiv_moduleUnboundedDerivedInverseImageIdIso_hom :
    conjugateEquiv Adjunction.id (moduleUnboundedDerivedAdjunction Λ (𝟙 X))
      (moduleUnboundedDerivedInverseImageIdIso Λ X).hom =
        (moduleUnboundedDerivedDirectImageIdIso Λ X).inv := rfl
end Identity

section Composition
variable {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- Localization of the original exact inverse-image compositor. -/
def moduleUnboundedDerivedInverseImageCompIso :
    moduleUnboundedDerivedInverseImage Λ (g ≫ f) ≅
      moduleUnboundedDerivedInverseImage Λ f ⋙ moduleUnboundedDerivedInverseImage Λ g :=
  Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ)) _ _ _ _
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (moduleInverseImageCompIso Λ f g) (.up ℤ))
        DerivedCategory.Q) ≪≫
    (Functor.mapDerivedCategoryCompIso (moduleInverseImage f Λ)
      (moduleInverseImage g Λ)).symm

/-- The structural compositor of the actual unbounded direct images.
It is the conjugate of the localized original inverse-image compositor. -/
def moduleUnboundedDerivedDirectImageCompIso :
    moduleUnboundedDerivedDirectImage Λ (g ≫ f) ≅
      moduleUnboundedDerivedDirectImage Λ g ⋙ moduleUnboundedDerivedDirectImage Λ f :=
  (conjugateIsoEquiv
    ((moduleUnboundedDerivedAdjunction Λ f).comp (moduleUnboundedDerivedAdjunction Λ g))
    (moduleUnboundedDerivedAdjunction Λ (g ≫ f))
    (moduleUnboundedDerivedInverseImageCompIso Λ f g)).symm

/-- Exact conjugacy of the original unbounded structural maps. -/
theorem conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom :
    conjugateEquiv
      ((moduleUnboundedDerivedAdjunction Λ f).comp (moduleUnboundedDerivedAdjunction Λ g))
      (moduleUnboundedDerivedAdjunction Λ (g ≫ f))
      (moduleUnboundedDerivedInverseImageCompIso Λ f g).hom =
        (moduleUnboundedDerivedDirectImageCompIso Λ f g).inv := rfl
end Composition
end AlgebraicGeometry.Scheme.EtaleCohomology
