/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityFactorization

/-! # Original unit normalization of the independent-model identity factorization -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dE dM
variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
  (hE : HasDerivedCategory.{dE} (ModuleSheaf X Λ))
  (hM : HasDerivedCategory.{dM} (ModuleSheaf X Λ))

/-- Both installed units and the original ordinary identity contraction are retained. -/
@[reassoc]
theorem moduleDerivedIdentityFactorizationIso_unit
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hM hE (moduleDirectImage (𝟙 X) Λ) _ _)).app
        ((moduleLowerShriek (𝟙 X) Λ).mapCochainComplexPlus.obj K) ≫
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hM hE (moduleDirectImage (𝟙 X) Λ) _ _)).map
        (((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hE hM (moduleLowerShriek (𝟙 X) Λ) _
          _)).app K) ≫
      (moduleDerivedIdentityFactorizationIso Λ X hE hM).hom.app (((@DerivedCategory.Plus.Q _ _ _
        hE)).obj K) =
    ((@DerivedCategory.Plus.Q _ _ _ hE)).map
      ((NatIso.mapCochainComplexPlus (moduleIdentityFactorizationIso Λ X)).hom.app K ≫
        (mapCochainComplexPlusIdIso (ModuleSheaf X Λ)).hom.app K) := by
  simpa only [moduleDerivedIdentityFactorizationIso,
    rightDerivedFunctorPlusCompUnit_app, Category.assoc, Functor.comp_obj,
    Functor.id_obj] using
    (@exactDerivedContractionViaIso_unit (ModuleSheaf X Λ) _ _ _ hE
      (ModuleSheaf X Λ) _ _ _ hM (moduleLowerShriek (𝟙 X) Λ)
      (moduleDirectImage (𝟙 X) Λ) _ _ _ (moduleIdentityFactorizationIso Λ X) K)

end AlgebraicGeometry.Scheme.EtaleCohomology
