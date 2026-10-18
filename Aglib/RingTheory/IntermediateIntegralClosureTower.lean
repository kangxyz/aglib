/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.CompleteDVRIntegralClosureTower

/-!
# An intermediate integral closure inside a specified upper closure

The map is the unique lift of the actual field inclusion. The upper ring is
kept literally unchanged, allowing degree induction through intermediate DVRs.
-/

@[expose] public noncomputable section

namespace IsIntegralClosure.IntermediateTower

variable (R S L E : Type*) [CommRing R] [CommRing S] [Field L] [Field E]
  [Algebra R S] [Algebra R L] [Algebra R E] [Algebra L E]
  [IsScalarTower R L E] [Algebra S E] [IsScalarTower R S E]
  [IsIntegralClosure S R E]

/-- The intermediate integral elements map to the specified upper integral closure. -/
@[instance_reducible] def closureAlgebra : Algebra (integralClosure R L) S :=
  (IsIntegralClosure.lift R S E : integralClosure R L →ₐ[R] S).toRingHom.toAlgebra

include E


/-- The lifted inclusion is compatible with the original base map. -/
theorem baseTower :
    let _ := closureAlgebra R S L E
    IsScalarTower R (integralClosure R L) S := by
  let _ := closureAlgebra R S L E
  exact IsScalarTower.of_algebraMap_eq fun x =>
    ((IsIntegralClosure.lift R S E : integralClosure R L →ₐ[R] S).commutes x).symm

/-- The lifted inclusion has exactly the original values in the upper field. -/
theorem topTower :
    let _ := closureAlgebra R S L E
    IsScalarTower (integralClosure R L) S E := by
  let _ := closureAlgebra R S L E
  exact IsScalarTower.of_algebraMap_eq fun x =>
    (IsIntegralClosure.algebraMap_lift R S E x).symm

omit [Algebra R S] [IsScalarTower R S E] in
/-- The same upper ring is the integral closure over the intermediate ring. -/
theorem upper_isIntegralClosure : IsIntegralClosure S (integralClosure R L) E :=
  IsIntegralClosure.tower_top (R := R)

/-- Finiteness is inherited by the actual intermediate ring. -/
theorem upper_finite [Module.Finite R S] :
    let _ := closureAlgebra R S L E
    Module.Finite (integralClosure R L) S := by
  let _ := closureAlgebra R S L E
  let _ := baseTower R S L E
  exact Module.Finite.of_restrictScalars_finite R _ _

/-- The actual lifted map is local when the specified upper ring is local. -/
-- Keep the upper-ring locality condition in the integral-closure tower API.
@[nolint unusedArguments]
theorem upper_isLocalHom [IsLocalRing S] :
    let _ := closureAlgebra R S L E
    IsLocalHom (algebraMap (integralClosure R L) S) := by
  let _ := closureAlgebra R S L E
  let _ := baseTower R S L E
  let _ := topTower R S L E
  let : IsIntegralClosure S (integralClosure R L) E := upper_isIntegralClosure R S L E
  have hi : (algebraMap (integralClosure R L) S).IsIntegral :=
    algebraMap_isIntegral_iff.mpr (IsIntegralClosure.isIntegral_algebra (integralClosure R L) E)
  apply hi.isLocalHom
  intro x y h
  apply Subtype.ext
  apply (algebraMap L E).injective
  change algebraMap (integralClosure R L) E x = algebraMap (integralClosure R L) E y
  simpa only [← IsScalarTower.algebraMap_apply] using
    congrArg (algebraMap S E) h

end IsIntegralClosure.IntermediateTower
