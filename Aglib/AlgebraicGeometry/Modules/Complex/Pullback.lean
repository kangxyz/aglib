/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Mathlib.Algebra.Homology.Additive

/-!
# Identity and composition for ordinary complex pullback

These are the actual module-sheaf pullback identity and composition isomorphisms
mapped degreewise to integer-indexed cochain complexes. Schemes and morphisms
are arbitrary, and no flatness, term bound or perfectness premise is imposed.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/PerfectComplexes/Pullback.lean`.
SHA-256: `358a8e272f6746d50fe8f2110bb397453d85777d8cb18c5027280bb2bf044351`.
Selected source lines: 137–149.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.Complex

/-- Geometric termwise pullback along an identity is the identity functor. -/
def pullbackIdIso (X : Scheme.{u}) : AlgebraicGeometry.Scheme.Modules.Complex.pullback (𝟙 X)
  ≅ 𝟭 (CochainComplex X.Modules ℤ) :=
  NatIso.mapHomologicalComplex (Scheme.Modules.pullbackId X) (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso X.Modules (ComplexShape.up ℤ)

/-- The actual geometric comparison for successive termwise pullbacks. -/
def pullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    AlgebraicGeometry.Scheme.Modules.Complex.pullback (f ≫ g) ≅
      AlgebraicGeometry.Scheme.Modules.Complex.pullback g ⋙
      AlgebraicGeometry.Scheme.Modules.Complex.pullback f :=
  (Functor.mapHomologicalComplexCompIso (Scheme.Modules.pullbackComp f g) _).symm

end AlgebraicGeometry.Scheme.Modules.Complex
