/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Finite.LocalPoints.Equiv
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteComponentPoint

/-! # Finite components indexed by points in one common algebraically closed field -/

@[expose] public noncomputable section

open IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u v w

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)]
  (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
  (Ω : Type w) [Field Ω] [IsAlgClosed Ω] [Algebra (ResidueField R) Ω]

/-- Reconstruct an actual geometric point from the maximal component it selects. -/
theorem finiteComponentPoint_geometricPointComponent (a : A →+* Ω)
    (ha : a.comp (algebraMap R A) =
      (algebraMap (ResidueField R) Ω).comp (residue R)) :
    finiteComponentPoint R A Ω (geometricPointComponent R A Ω a ha) = a :=
  Algebra.FiniteLocalPoints.finiteComponentPoint_geometricPointComponent R A Ω a ha

/-- Maximal components and actual geometric points over the fixed closed base
point are in bijection. All geometric points use the same field `Ω`. -/
def finiteComponentPointEquiv : MaximalSpectrum A ≃
    {a : A →+* Ω // a.comp (algebraMap R A) =
      (algebraMap (ResidueField R) Ω).comp (residue R)} :=
  Algebra.FiniteLocalPoints.finiteComponentPointEquiv R A Ω

end AlgebraicGeometry.Scheme.EtaleCohomology
