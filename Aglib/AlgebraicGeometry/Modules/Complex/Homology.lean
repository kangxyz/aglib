/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Homology of actual derived and restricted module complexes

A native derived isomorphism induces an isomorphism of the original homology
sheaves through the native homology factorization. Ordinary exact restriction
commutes with homology through its actual mapHomologyIso.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/Homology.lean`,
archive SHA-256
`16c127c5b7a5874cb4d841e1161b436190c35aeb08802b89cb19fd8c76ad1d48`,
source SHA-256 `bfb93dda9ff5df57674129b0a5255631ac11bebebaab26d50426b51f4fdbaf34`.
The accepted consumer-retargeted input has SHA-256
`5c3aa2c2a65dfad3868fb1cb2e0114e3bf41693497a51c3497640d7e6d0b5d8a`.
Admitted subset: homologyIsoOfDerivedIso and restrictHomologyIso.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Complex

/-- The same constructed native derived model in morphism universe `u + 1`. -/
local instance standardDerivedHomology (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- An isomorphism in the original quasi-isomorphism localization induces
an isomorphism on the actual sheaf homology. -/
def homologyIsoOfDerivedIso {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    (e : (DerivedCategory.Q (C := X.Modules)).obj K ≅ (DerivedCategory.Q (C := X.Modules)).obj L)
      (i : ℤ) :
    K.homology i ≅ L.homology i :=
  ((DerivedCategory.homologyFunctorFactors X.Modules i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor X.Modules i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors X.Modules i).app L

/-- Actual open restriction commutes with sheaf homology. -/
def restrictHomologyIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : CochainComplex X.Modules ℤ) (i : ℤ) :
    ((restrict j).obj K).homology i ≅ (Scheme.Modules.restrictFunctor j).obj (K.homology i) :=
  (K.sc i).mapHomologyIso (Scheme.Modules.restrictFunctor j)


end AlgebraicGeometry.Scheme.Modules.Complex
