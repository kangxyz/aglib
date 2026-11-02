/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityFactorization
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExactDerivedContractionAdjunction

/-! # Identity factorization as the inverse original adjunction unit

The contraction is the inverse unit for `J_id! ⊣ R_id`, equivalently the
counit of the reversed adjoint equivalence. It is not the counit of `J_id! ⊣ R_id`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dE dM
variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})

/-- The original inverse-image adjunction transported by the original identity comparisons. -/
def moduleIdentityFactorizationAdjunction :
    moduleLowerShriek (𝟙 X) Λ ⊣ moduleDirectImage (𝟙 X) Λ :=
  (moduleInverseImageAdjunction (𝟙 X) Λ).ofNatIsoLeft
    (moduleInverseImageIdIso Λ X ≪≫ (moduleLowerShriekIdIso Λ X).symm)

/-- This transported original unit is inverse to the original ordinary contraction. -/
theorem moduleIdentityFactorizationAdjunction_unit (M : ModuleSheaf X Λ) :
    (moduleIdentityFactorizationAdjunction Λ X).unit.app M ≫
      (moduleIdentityFactorizationIso Λ X).hom.app M = 𝟙 M := by
  simpa [moduleIdentityFactorizationAdjunction, moduleIdentityFactorizationIso,
    Adjunction.ofNatIsoLeft, Category.assoc, ← Functor.map_comp_assoc] using
    moduleInverseImageIdIso_unit Λ X M

variable (hE : HasDerivedCategory.{dE} (ModuleSheaf X Λ))
  (hM : HasDerivedCategory.{dM} (ModuleSheaf X Λ))

/-- Deriving the original transported adjunction with independent endpoint and middle models. -/
def moduleDerivedIdentityFactorizationAdjunction :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hE hM (moduleLowerShriek (𝟙 X) Λ) _ _) ⊣
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hM hE (moduleDirectImage (𝟙 X) Λ) _ _) :=
  @Adjunction.rightDerivedFunctorPlus (ModuleSheaf X Λ) _ _ hE _
    (ModuleSheaf X Λ) _ _ hM _ (moduleLowerShriek (𝟙 X) Λ)
    (moduleDirectImage (𝟙 X) Λ) _ _ _ (moduleIdentityFactorizationAdjunction Λ X)

/-- The existing derived contraction is exactly the inverse original derived adjunction unit. -/
theorem moduleDerivedIdentityFactorizationAdjunction_unit_eq_inv :
    (moduleDerivedIdentityFactorizationAdjunction Λ X hE hM).unit =
      (moduleDerivedIdentityFactorizationIso Λ X hE hM).inv := by
  dsimp only [moduleDerivedIdentityFactorizationAdjunction,
    moduleDerivedIdentityFactorizationIso]
  exact @exactDerivedContractionViaIso_adjunction_unit_eq_inv
    (ModuleSheaf X Λ) _ _ _ hE (ModuleSheaf X Λ) _ _ _ hM
    (moduleLowerShriek (𝟙 X) Λ) (moduleDirectImage (𝟙 X) Λ) _ _ _ _
    (moduleIdentityFactorizationAdjunction Λ X) (moduleIdentityFactorizationIso Λ X)
    (moduleIdentityFactorizationAdjunction_unit Λ X)

end AlgebraicGeometry.Scheme.EtaleCohomology
