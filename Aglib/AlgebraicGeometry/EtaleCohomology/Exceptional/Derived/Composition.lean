/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIdentityCoherence
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.DerivedConjugacy
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.IdentityConjugacy

/-!
# Original identity and composition for derived constant-ring module images

The genuine module image comparisons induce the native bounded-below derived
comparisons. Direct-image composition uses preservation of injective objects,
not exactness of arbitrary direct image. The original inverse/direct identity
and composition comparisons remain conjugate under the installed derived
adjunctions. These are the comparisons used by compactification refinement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wT

variable (Λ : Type (u + 1)) [Ring Λ]

section Identity

variable (X : Scheme.{u}) [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The original inverse-image identity induces the installed derived identity. -/
def moduleDerivedInverseImageIdIso :
    moduleDerivedInverseImage Λ (𝟙 X) ≅ 𝟭 (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  (moduleInverseImage (𝟙 X) Λ).rightDerivedFunctorPlusIso (moduleInverseImageIdIso Λ X) ≪≫
    Functor.rightDerivedFunctorPlusIdIso (ModuleSheaf X Λ)

/-- The original direct-image identity induces the installed derived identity. -/
def moduleDerivedDirectImageIdIso :
    moduleDerivedDirectImage Λ (𝟙 X) ≅ 𝟭 (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  (moduleDirectImage (𝟙 X) Λ).rightDerivedFunctorPlusIso (moduleDirectImageIdIso Λ X) ≪≫
    Functor.rightDerivedFunctorPlusIdIso (ModuleSheaf X Λ)

/-- The derived identity comparisons are conjugate for the original derived adjunction. -/
theorem conjugateEquiv_moduleDerivedInverseImageIdIso_hom :
    conjugateEquiv Adjunction.id (moduleDerivedAdjunction Λ (𝟙 X))
      (moduleDerivedInverseImageIdIso Λ X).hom = (moduleDerivedDirectImageIdIso Λ X).inv :=
  (moduleInverseImageAdjunction (𝟙 X) Λ).rightDerivedFunctorPlus_conjugate_id
    (moduleInverseImageIdIso Λ X) (moduleDirectImageIdIso Λ X)
    (conjugateEquiv_moduleInverseImageIdIso_hom Λ X)

end Identity

section Composition

variable {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- Derived inverse images compose through their original exact module comparison. -/
def moduleDerivedInverseImageCompIso :
    moduleDerivedInverseImage Λ (g ≫ f) ≅
      moduleDerivedInverseImage Λ f ⋙ moduleDerivedInverseImage Λ g :=
  (moduleInverseImage (g ≫ f) Λ).rightDerivedFunctorPlusIso
      (moduleInverseImageCompIso Λ f g) ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
      (moduleInverseImage f Λ) (moduleInverseImage g Λ)

/-- Derived direct images compose through their original injective-preserving comparison. -/
def moduleDerivedDirectImageCompIso :
    moduleDerivedDirectImage Λ (g ≫ f) ≅
      moduleDerivedDirectImage Λ g ⋙ moduleDerivedDirectImage Λ f :=
  (moduleDirectImage (g ≫ f) Λ).rightDerivedFunctorPlusIso
      (moduleDirectImageCompIso Λ f g) ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
      (moduleDirectImage g Λ) (moduleDirectImage f Λ)

/-- The two original composition comparisons remain conjugate after deriving. -/
theorem conjugateEquiv_moduleDerivedInverseImageCompIso_hom :
    conjugateEquiv ((moduleDerivedAdjunction Λ f).comp (moduleDerivedAdjunction Λ g))
      (moduleDerivedAdjunction Λ (g ≫ f)) (moduleDerivedInverseImageCompIso Λ f g).hom =
        (moduleDerivedDirectImageCompIso Λ f g).inv :=
  Adjunction.rightDerivedFunctorPlus_conjugate_comp
    (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction g Λ)
    (moduleInverseImageAdjunction (g ≫ f) Λ)
    (moduleInverseImageCompIso Λ f g) (moduleDirectImageCompIso Λ f g).symm
    (conjugateEquiv_moduleInverseImageCompIso_hom Λ f g)

end Composition

end AlgebraicGeometry.Scheme.EtaleCohomology
