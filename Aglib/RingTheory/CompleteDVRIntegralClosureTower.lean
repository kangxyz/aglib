/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.CompleteDVRExtension

/-!
# Literal integral-closure towers over a complete DVR

The upper ring is the integral closure of the original base, not a replacement
ring. Its algebra structure is the restriction of the actual field map. Native
integral-closure transitivity identifies that same ring as the closure over the
intermediate ring. Completeness is an explicit hypothesis throughout.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing.IntegralClosureTower

open IsLocalRing

section Maps

variable (R L D : Type*) [CommRing R] [Field L] [Field D]
  [Algebra R L] [Algebra R D] [Algebra L D] [IsScalarTower R L D]

/-- The literal field map restricted to the two actual integral closures. -/
@[instance_reducible] def closureAlgebra : Algebra (integralClosure R L) (integralClosure R D) :=
  (IsScalarTower.toAlgHom R L D).mapIntegralClosure.toRingHom.toAlgebra

attribute [local instance] closureAlgebra

/-- The restricted map commutes with the original base maps. -/
instance baseTower : IsScalarTower R (integralClosure R L) (integralClosure R D) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    ((IsScalarTower.toAlgHom R L D).mapIntegralClosure.commutes x).symm

/-- The restricted map has precisely the original values in the top field. -/
instance topTower : IsScalarTower (integralClosure R L) (integralClosure R D) D :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- No abstract identification of integral closures is introduced. -/
theorem upper_isIntegralClosure :
    IsIntegralClosure (integralClosure R D) (integralClosure R L) D :=
  IsIntegralClosure.tower_top (R := R)

/-- The upper local homomorphism is the actual restriction of the field map. -/
theorem upper_isLocalHom :
    IsLocalHom (algebraMap (integralClosure R L) (integralClosure R D)) :=
  IsDiscreteValuationRing.CompleteExtension.mapIntegralClosure_isLocalHom
    (IsScalarTower.toAlgHom R L D)

/-- Compatibility with the actual field inclusion is literal equality. -/
theorem upper_map_apply (x : integralClosure R L) :
    algebraMap (integralClosure R D) D
      (algebraMap (integralClosure R L) (integralClosure R D) x) =
        algebraMap L D (algebraMap (integralClosure R L) L x) := rfl

end Maps

section Complete

variable (R F L D : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Field D] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  [Algebra F D] [Algebra R D] [IsScalarTower R F D]
  [Algebra L D] [IsScalarTower R L D] [IsScalarTower F L D]
  [FiniteDimensional F L] [FiniteDimensional F D]
  [Algebra.IsSeparable F L] [Algebra.IsSeparable F D]

attribute [local instance] closureAlgebra

include F

omit [IsAdicComplete (maximalIdeal R) R] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [IsScalarTower F L D]
  [Algebra F L] [IsScalarTower R F L] in
/-- Finiteness of the literal upper ring over the literal intermediate ring. -/
theorem upper_finite : Module.Finite (integralClosure R L) (integralClosure R D) := by
  let : Module.Finite R (integralClosure R D) :=
    IsIntegralClosure.finite R F D (integralClosure R D)
  exact Module.Finite.of_restrictScalars_finite R _ _

omit [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [FiniteDimensional F D]
  [Algebra.IsSeparable F L] [Algebra.IsSeparable F D] [IsScalarTower F L D]
  [Algebra F D] [IsScalarTower R F D] in
/-- Torsion-freeness uses the embedding of the actual upper ring in its field. -/
theorem upper_torsionFree :
    Module.IsTorsionFree (integralClosure R L) (integralClosure R D) := by
  let : IsFractionRing (integralClosure R L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R F L (integralClosure R L)
  let : IsIntegralClosure (integralClosure R D) (integralClosure R L) D :=
    upper_isIntegralClosure R L D
  exact IsIntegralClosure.isTorsionFree (integralClosure R L) D

end Complete

end IsDiscreteValuationRing.IntegralClosureTower
