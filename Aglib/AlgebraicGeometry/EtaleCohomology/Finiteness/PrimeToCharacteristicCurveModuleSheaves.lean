/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PrimeToCharacteristicCurveModules
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantUnderlyingCohomology

/-!
# Finite original H1 of prime-to-characteristic constant module sheaves

The native constant `ModuleCat`-valued sheaf has finite original underlying
abelian H1 for its actual coefficient-ring action. The native scalar-linear
constant-underlying comparison transports the constant-coefficient theorem;
the coefficient ring has an independent universe and need not be Noetherian.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness

universe u e l

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Finite literal modules killed by an invertible prime give finite original
H1 of their actual constant module sheaves on a smooth proper geometric curve. -/
theorem constantModuleSheaf_h1_finite_of_prime_nsmul
    {k : Type u} [Field k] [IsSepClosed k] (X : FScheme k) (hX : Properties X)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X.left)]
    [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{e}]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k))
    (Λ : Type l) [CommRing Λ] (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, p • x = 0) :
    Module.Finite Λ ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology Λ 1).obj
      ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
  (ModuleCat.Sheaf.finite_cohomology_constant_iff X.left.smallEtaleTopology Λ 1 M).mpr
    (constantModule_h1_finite_of_prime_nsmul X hX p hunit Λ M hM)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness
