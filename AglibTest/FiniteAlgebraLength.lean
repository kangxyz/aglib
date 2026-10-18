/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.FiniteAlgebraLength
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Consumers of the actual finite closed-fiber length formula

Arbitrary finite-length ideal quotients and a two-branch algebra over a field
exercise the actual all-point sum. The two branches have the same base point.
-/

@[expose] public section

noncomputable section

namespace AglibTest.FiniteAlgebraLength

open Module

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [IsLocalRing R]
  [IsNoetherianRing R] [CommRing S] [Algebra R S] [Module.Finite R S]

/-- Any actual finite-length closed support quotient satisfies the all-point formula. -/
theorem closedSupportQuotient (I : Ideal S) (hI : Module.length S (S ⧸ I) ≠ ⊤) :
    Module.length R (S ⧸ I) = finiteAlgebraFiberLengthSum (M := S ⧸ I) R S :=
  finiteAlgebra_length_eq_fiberSum R S hI

/-- The base length of the actual closed support quotient is genuinely finite. -/
theorem closedSupportQuotientFinite (I : Ideal S)
    (hI : Module.length S (S ⧸ I) ≠ ⊤) : Module.length R (S ⧸ I) ≠ ⊤ :=
  finiteAlgebra_length_ne_top R S hI

/-- Powers of an actual maximal ideal give finite-length nilpotent thickenings;
their fiber formula uses the full quotient, without replacing it by its reduction. -/
theorem maximalThickening (p : MaximalSpectrum S) (n : ℕ) :
    Module.length R (S ⧸ p.asIdeal ^ n) =
      finiteAlgebraFiberLengthSum (M := S ⧸ p.asIdeal ^ n) R S := by
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  apply finiteAlgebra_length_eq_fiberSum R S
  apply Module.length_ne_top_of_support_isMaximal
  intro q hq
  have hpq : p.asIdeal ^ n ≤ q.asIdeal := by
    simpa only [Ideal.annihilator_quotient] using
      Module.annihilator_le_of_mem_support hq
  exact p.isMaximal.eq_of_le q.isPrime.ne_top (Ideal.IsPrime.le_of_pow_le hpq) ▸
    p.isMaximal

/-- A finite algebra with two branches above one field point contributes
total multiplicity two to the actual localized residue-weighted sum. -/
theorem twoBranchCollision (K : Type u) [Field K] :
    finiteAlgebraFiberLengthSum (M := K × K) K (K × K) = 2 := by
  have : IsArtinianRing (K × K) := IsArtinianRing.of_finite K (K × K)
  rw [← finiteAlgebra_length_eq_fiberSum K (K × K) Module.length_ne_top,
    Module.length_eq_finrank, Module.finrank_prod]
  simp

end AglibTest.FiniteAlgebraLength
