/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Residue-field points of a spectrum

`Spec.map_algebraMap_residueField_closedPoint`: for a prime `P` of a commutative ring `A`, the
morphism `Spec κ(P) ⟶ Spec A` induced by the residue map sends the closed point to `P`.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry

/-- The closed point of the residue field of a prime maps to that prime. -/
theorem AlgebraicGeometry.Spec.map_algebraMap_residueField_closedPoint {A : CommRingCat.{u}}
    (P : Ideal A) [P.IsPrime] :
    Spec.map (CommRingCat.ofHom (algebraMap A P.ResidueField))
      (IsLocalRing.closedPoint P.ResidueField) = ⟨P, inferInstance⟩ := by
  apply PrimeSpectrum.ext
  change (IsLocalRing.maximalIdeal P.ResidueField).comap (algebraMap A P.ResidueField) = P
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
    Ideal.ker_algebraMap_residueField]

