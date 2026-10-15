/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.ExtensionByZero
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
/-!
# Open restriction preserves injective module sheaves

The genuine extension-by-zero adjunction and its established exactness imply
that original open restriction preserves injective objects. This applies to
all module sheaves and arbitrary open immersions, without compactness,
quasicoherence or separation hypotheses.
-/
@[expose] public section


noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- Open restriction preserves injectives because its genuine left adjoint is exact. -/
instance restrictFunctor_preservesInjectiveObjects {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (extensionByZeroRestrictAdjunction j)

/-- The original restricted sheaf is injective on every open, with no compactness hypothesis. -/
lemma injective_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) [Injective M] : Injective (M.restrict j) :=
  Functor.injective_obj (Scheme.Modules.restrictFunctor j) M

end AlgebraicGeometry.Scheme.Modules
