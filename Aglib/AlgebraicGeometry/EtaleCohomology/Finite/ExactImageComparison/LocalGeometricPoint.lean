/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Finite.LocalPoints.LocalPoint
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteFiberIndex

/-! # The actual geometric point of a finite local component

The chosen residue embedding gives a literal ring map from the finite local
component. Its uniqueness is expressed using the original base ring map,
without identifying the component residue field with the geometric field.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u v w

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)]
  (C : Type v) [CommRing C] [IsLocalRing C] [Algebra R C] [Module.Finite R C]
  [IsLocalHom (algebraMap R C)]
  (Ω : Type w) [Field Ω] [IsAlgClosed Ω] [Algebra (ResidueField R) Ω]

/-- The actual ring map defining the geometric point of a finite local component. -/
def finiteLocalGeometricPoint : C →+* Ω :=
  Algebra.FiniteLocalPoints.finiteLocalGeometricPoint R C Ω

/-- The geometric point lies over the original base residue map. -/
theorem finiteLocalGeometricPoint_comp_algebraMap :
    (finiteLocalGeometricPoint R C Ω).comp (algebraMap R C) =
      (algebraMap (ResidueField R) Ω).comp (residue R) :=
  Algebra.FiniteLocalPoints.finiteLocalGeometricPoint_comp_algebraMap R C Ω

/-- Any local map from the component into the same geometric field, lying over
that original base map, is the chosen geometric point. -/
theorem finiteLocalGeometricPoint_unique (a : C →+* Ω) [IsLocalHom a]
    (ha : a.comp (algebraMap R C) =
      (algebraMap (ResidueField R) Ω).comp (residue R)) :
    a = finiteLocalGeometricPoint R C Ω :=
  Algebra.FiniteLocalPoints.finiteLocalGeometricPoint_unique R C Ω a ha

end AlgebraicGeometry.Scheme.EtaleCohomology
