/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityFactorization

/-! # Native normalization through independent intermediate derived models -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Functor
universe u₁ u₂ u₃ v₁ v₂ v₃ d₁ d₂ d₃
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{d₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [EnoughInjectives B]
  [HasDerivedCategory.{d₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{d₃} C]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
  [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)

/-- Contract the original derived composite by its original ordinary isomorphism. -/
def derivedCompositeNormalizeOfPreservesInjectives [F.PreservesInjectiveObjects] :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅ H.rightDerivedFunctorPlus :=
  (F.rightDerivedFunctorPlusCompIsoOfPreservesInjectives G).symm ≪≫
    (F ⋙ G).rightDerivedFunctorPlusIso e

/-- Exactness of the second factor suffices for the same original contraction. -/
def derivedCompositeNormalizeOfPreservesHomology [G.PreservesHomology] :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅ H.rightDerivedFunctorPlus :=
  (F.rightDerivedFunctorPlusCompIsoOfPreservesHomology G).symm ≪≫
    (F ⋙ G).rightDerivedFunctorPlusIso e
end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dX dS dM
variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{dX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{dS} (ModuleSheaf S Λ))

/-- The literal proper factorization contracts without identifying either source model. -/
def moduleDerivedProperNormalizationIso
    (hM : HasDerivedCategory.{dM} (ModuleSheaf X Λ)) :
    (@rightDerivedFunctorPlus _ _ _ _ _ _ hX hM (moduleLowerShriek (𝟙 X) Λ) _ _) ⋙
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hM hS (moduleDirectImage f Λ) _ _) ≅
        (@rightDerivedFunctorPlus _ _ _ _ _ _ hX hS (moduleDirectImage f Λ) _ _) := by
  let : (moduleLowerShriek (𝟙 X) Λ).IsEquivalence :=
    Functor.isEquivalence_of_iso (moduleLowerShriekIdIso Λ X).symm
  exact @derivedCompositeNormalizeOfPreservesInjectives
    (ModuleSheaf X Λ) _ _ _ hX (ModuleSheaf X Λ) _ _ _ hM
    (ModuleSheaf S Λ) _ _ hS _ _ _ _ _ _
    (Functor.isoWhiskerRight (moduleLowerShriekIdIso Λ X) _ ≪≫ Functor.leftUnitor _) _

/-- The raw open factorization contracts without identifying either target model. -/
def moduleDerivedOpenNormalizationIso [IsOpenImmersion f]
    (hM : HasDerivedCategory.{dM} (ModuleSheaf S Λ)) :
    (@rightDerivedFunctorPlus _ _ _ _ _ _ hX hM (moduleLowerShriek f Λ) _ _) ⋙
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hM hS (moduleDirectImage (𝟙 S) Λ) _ _) ≅
        (@rightDerivedFunctorPlus _ _ _ _ _ _ hX hS (moduleLowerShriek f Λ) _ _) :=
  @derivedCompositeNormalizeOfPreservesHomology
    (ModuleSheaf X Λ) _ _ _ hX (ModuleSheaf S Λ) _ _ _ hM
    (ModuleSheaf S Λ) _ _ hS _ _ _ _ _ _
    (Functor.isoWhiskerLeft _ (moduleDirectImageIdIso Λ S) ≪≫ Functor.rightUnitor _) _

end AlgebraicGeometry.Scheme.EtaleCohomology
