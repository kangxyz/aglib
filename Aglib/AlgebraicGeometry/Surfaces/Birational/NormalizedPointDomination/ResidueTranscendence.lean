/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteType.ResidueField
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Original residue maps and transcendence after finite extensions

A closed point of a locally finite-type scheme morphism has finite extension
of the original image residue field. For composable original scheme arrows,
transcendence over the bottom residue field persists over this finite
intermediate residue extension. The native residue-map composition equation
installs the scalar tower; no unrelated field embeddings are chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

/-- Finiteness of the actual residue-field map at an actual closed source
point of a locally finite-type morphism. -/
theorem residueFieldMap_finite_of_closedPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) : (f.residueFieldMap x).hom.Finite :=
  f.residueFieldMap_finite_of_closedPoint x hx

/-- Transcendence survives the finite intermediate extension for the original
residue maps of a composable pair of actual scheme morphisms. -/
theorem transcendental_residueFieldMap_of_finite
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hfin : (g.residueFieldMap (f x)).hom.Finite) (a : X.residueField x)
    (ha : letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
        ((f ≫ g).residueFieldMap x).hom.toAlgebra
      Transcendental (Z.residueField (g (f x))) a) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Transcendental (Y.residueField (f x)) a := by
  let K := Z.residueField (g (f x))
  let L := Y.residueField (f x)
  let E := X.residueField x
  let : Algebra K L := (g.residueFieldMap (f x)).hom.toAlgebra
  let : Algebra L E := (f.residueFieldMap x).hom.toAlgebra
  let : Algebra K E := ((f ≫ g).residueFieldMap x).hom.toAlgebra
  let : Module.Finite K L := hfin
  let : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq (fun b ↦ by
    exact congrArg (fun k : K ⟶ E ↦ k b) (residueFieldMap_comp f g x))
  exact ha.extendScalars L

/-- The closed-point hypothesis derives the finite residue extension used
in the original-map transcendence compatibility theorem. -/
theorem transcendental_residueFieldMap_of_closedPoint
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType g] (x : X)
    (hx : IsClosed ({f x} : Set Y)) (a : X.residueField x)
    (ha : letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
        ((f ≫ g).residueFieldMap x).hom.toAlgebra
      Transcendental (Z.residueField (g (f x))) a) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Transcendental (Y.residueField (f x)) a :=
  transcendental_residueFieldMap_of_finite f g x
    (residueFieldMap_finite_of_closedPoint g (f x) hx) a ha

end AlgebraicGeometry.Scheme.NormalizedPointDomination
