/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-! # The component selected by a geometric point of a finite algebra

The kernel of an actual geometric point lying over the closed base point is
maximal by integrality. This supplies the map to the finite-component index,
without assuming the geometric point map itself surjective.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u v w

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
  (Ω : Type w) [Field Ω] [Algebra (ResidueField R) Ω]
  (a : A →+* Ω)
  (ha : a.comp (algebraMap R A) =
    (algebraMap (ResidueField R) Ω).comp (residue R))

include ha

omit [Module.Finite R A] in
/-- The selected prime lies over the original closed point of the base. -/
theorem geometricPointKernel_comap :
    (RingHom.ker a).comap (algebraMap R A) = maximalIdeal R := by
  rw [RingHom.comap_ker, ha,
    RingHom.ker_comp_of_injective _ (algebraMap (ResidueField R) Ω).injective,
    ker_residue]

/-- A point over the closed point of an integral algebra has maximal kernel. -/
theorem geometricPointKernel_isMaximal : (RingHom.ker a).IsMaximal := by
  let : (RingHom.ker a).IsPrime := RingHom.ker_isPrime a
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R)
  change ((RingHom.ker a).comap (algebraMap R A)).IsMaximal
  rw [geometricPointKernel_comap R A Ω a ha]
  infer_instance

/-- The actual finite local component selected by the geometric point. -/
def geometricPointComponent : MaximalSpectrum A :=
  ⟨RingHom.ker a, geometricPointKernel_isMaximal R A Ω a ha⟩

/-- For a local finite algebra, lying over the closed base point already makes
its geometric point a local homomorphism. -/
theorem geometricPoint_isLocalHom [IsLocalRing A] : IsLocalHom a := by
  apply ((local_hom_TFAE a).out 5 1).mp
  rw [maximalIdeal_eq_bot]
  change RingHom.ker a = maximalIdeal A
  exact eq_maximalIdeal (geometricPointKernel_isMaximal R A Ω a ha)

end AlgebraicGeometry.Scheme.EtaleCohomology
