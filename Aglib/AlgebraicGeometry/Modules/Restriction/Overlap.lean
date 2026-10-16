/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion

/-!
# Restriction comparison on an overlap

The canonical comparison between two iterated restrictions uses the same chosen pullback of the
two open immersions and its two projection maps.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/GluingSubobjects.lean`.
SHA-256: `d6329afc8058687c07b626f0cf1a82a708d6ed99bcdda9d8fc260402bd0c28a9`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical identification of the two restrictions of an ambient
module to the actual overlap. -/
def overlapRestrictIso
    {U V X : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a] :
    restrictFunctor j ⋙ restrictFunctor (pullback.fst j a) ≅
      restrictFunctor a ⋙ restrictFunctor (pullback.snd j a) :=
  (restrictFunctorComp (pullback.fst j a) j).symm ≪≫
    restrictFunctorCongr (pullback.condition (f := j) (g := a)) ≪≫
    restrictFunctorComp (pullback.snd j a) a

end AlgebraicGeometry.Scheme.Modules
