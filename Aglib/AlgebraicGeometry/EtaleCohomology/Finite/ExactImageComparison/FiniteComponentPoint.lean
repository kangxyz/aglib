/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Finite.LocalPoints.Component
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.LocalGeometricPoint
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.GeometricPointKernel

/-! # The common geometric point attached to an actual finite local component -/

@[expose] public noncomputable section

open IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u v w

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)]
  (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
  (Ω : Type w) [Field Ω] [IsAlgClosed Ω] [Algebra (ResidueField R) Ω]
  (m : MaximalSpectrum A)

/-- The point of the finite algebra obtained from the original maximal localization
and its unique residue embedding into the chosen algebraically closed field. -/
def finiteComponentPoint : A →+* Ω :=
  Algebra.FiniteLocalPoints.finiteComponentPoint R A Ω m

/-- This is an actual point over the fixed base geometric point. -/
theorem finiteComponentPoint_comp_algebraMap :
    (finiteComponentPoint R A Ω m).comp (algebraMap R A) =
      (algebraMap (ResidueField R) Ω).comp (residue R) :=
  Algebra.FiniteLocalPoints.finiteComponentPoint_comp_algebraMap R A Ω m

/-- The constructed common-field point selects exactly the prescribed component. -/
theorem finiteComponentPoint_ker :
    RingHom.ker (finiteComponentPoint R A Ω m) = m.asIdeal :=
  Algebra.FiniteLocalPoints.finiteComponentPoint_ker R A Ω m

/-- Distinct finite local components give distinct actual common-field points. -/
theorem finiteComponentPoint_injective : Function.Injective (finiteComponentPoint R A Ω) :=
  Algebra.FiniteLocalPoints.finiteComponentPoint_injective R A Ω

end AlgebraicGeometry.Scheme.EtaleCohomology
