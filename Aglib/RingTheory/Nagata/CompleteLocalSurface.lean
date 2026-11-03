/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.CompleteLocal

/-! # Dimension-two compatibility for complete local normalization and Nagata results -/

@[expose] public noncomputable section

open IsLocalRing

universe u v

/-- A complete Noetherian local domain of dimension at most two is
Japanese. Its normality is derived only for the actual regular source
constructed in dimension two, not assumed for the original domain. -/
theorem IsJapaneseRing.of_complete_local_dimLE_two
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 2 A]
    [IsAdicComplete (maximalIdeal A) A] : IsJapaneseRing.{u, 0} A := by
  exact IsJapaneseRing.of_complete_local_dimLE 2 A
    (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 A))

/-- Every complete Noetherian local ring of dimension at most two is
Nagata. Every tested prime quotient is the actual quotient, with its
original maximal-adic completeness and fraction-field coefficient map. -/
theorem IsNagataRing.of_complete_local_dimLE_two
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Ring.KrullDimLE 2 A] [IsAdicComplete (maximalIdeal A) A] :
    IsNagataRing.{u, 0} A := by
  exact IsNagataRing.of_complete_local_dimLE 2 A
    (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 A))

/-- CN2 for the literal integral closure in any finite extension of a
supplied actual fraction field. The original action of the complete
local domain on the ambient extension field is unchanged. -/
theorem integralClosure.finite_of_complete_local_dimLE_two
    (A K L : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 2 A]
    [IsAdicComplete (maximalIdeal A) A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] : Module.Finite A (integralClosure A L) :=
  (IsJapaneseRing.of_complete_local_dimLE_two A).finite_integralClosure_of_isFractionRing K L

/-- A local domain finite over the original complete local ring of
dimension at most two has reduced maximal-adic completion. This uses
finite Nagata ascent and the proved dimension-bounded completion theorem;
the finite algebra itself need not be normal or complete. -/
theorem AdicCompletion.isReduced_of_finite_over_complete_local_dimLE_two
    (A B : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Ring.KrullDimLE 2 A] [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B] [Module.Finite A B] :
    IsReduced (AdicCompletion (maximalIdeal B) B) := by
  have hB : IsNagataRing.{u, 0} B :=
    (IsNagataRing.of_complete_local_dimLE_two A).of_finite
  exact hB.isReduced_completion

/-- CR2: the literal normalization of a complete reduced Noetherian local
ring of dimension at most two in its original total quotient ring is finite. -/
theorem integralClosure.finite_of_complete_local_reduced_dimLE_two
    (R : Type u) [CommRing R] [IsReduced R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 2 R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (Q : Type v) [CommRing Q] [Algebra R Q] [IsFractionRing R Q] :
    Module.Finite R (integralClosure R Q) :=
  integralClosure.finite_of_isNagataRing R (IsNagataRing.of_complete_local_dimLE_two R) Q
