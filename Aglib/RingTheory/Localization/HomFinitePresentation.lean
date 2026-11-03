/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Native Hom localization with the original additive monoids

The native finite-presentation localization theorem applies to the given
monoid and module parents. Ring-induced additive groups are used only inside
the property proof; the original scalar-extension map is unchanged.
-/

@[expose] public noncomputable section

namespace IsLocalizedModule

/-- Native Hom localization for the given additive monoids and module actions.
The ring-induced groups are needed only inside the finite-presentation proof. -/
theorem mapExtendScalars_of_finitePresentation
    {R : Type*} [CommRing R] (S : Submonoid R)
    {M M' N N' : Type*}
    [AddCommMonoid M] [AddCommMonoid M']
    [AddCommMonoid N] [AddCommMonoid N']
    [Module R M] [Module R M'] [Module R N] [Module R N']
    (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (g : N →ₗ[R] N') [IsLocalizedModule S g]
    (D : Type*) [CommRing D] [Algebra R D]
    [Module D M'] [Module D N']
    [IsScalarTower R D M'] [IsScalarTower R D N'] [IsLocalization S D]
    [Module.FinitePresentation R M] :
    IsLocalizedModule S (IsLocalizedModule.mapExtendScalars S f g D) := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R (M := M)
  let : AddCommGroup M' := Module.addCommMonoidToAddCommGroup R (M := M')
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R (M := N)
  let : AddCommGroup N' := Module.addCommMonoidToAddCommGroup R (M := N')
  exact Module.FinitePresentation.isLocalizedModule_mapExtendScalars S f g D

end IsLocalizedModule
