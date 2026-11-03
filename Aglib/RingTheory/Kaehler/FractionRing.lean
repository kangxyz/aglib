/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.FractionRing


/-!
# RingTheory / Kaehler / FractionRing

Source: `FiniteCoefficientExpansion/FractionRing.lean`.
Incoming SHA256: `bf7c1f54f7f82ac2f4c9fdb9f42fb0925a21bdd75039d6568465eb2639e7ce52`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open Module


namespace KaehlerDifferential

section UnchangedBase

variable {Λ A K ι : Type*} [CommRing Λ] [CommRing A] [IsDomain A]
  [Field K] [Algebra Λ A] [Algebra A K] [Algebra Λ K]
  [IsScalarTower Λ A K] [IsFractionRing A K]

/-- Localize the actual ordinary differential basis without changing the base ring. -/
def fractionBasis (b : Module.Basis ι A (KaehlerDifferential Λ A)) :
    Module.Basis ι K (KaehlerDifferential Λ K) := by
  let : Algebra.FormallyEtale A K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  exact (b.baseChange K).map (tensorKaehlerEquivOfFormallyEtale Λ A K)

omit [IsDomain A] in
/-- The coordinate formula retains the original base and original fraction inclusion. -/
theorem fractionBasis_repr_D (b : Module.Basis ι A (KaehlerDifferential Λ A))
    (a : A) (i : ι) :
    (fractionBasis (K := K) b).repr (D Λ K (algebraMap A K a)) i =
      algebraMap A K (b.repr (D Λ A a) i) := by
  let : Algebra.FormallyEtale A K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  change (b.baseChange K).repr
    ((tensorKaehlerEquivOfFormallyEtale Λ A K).symm
      (D Λ K (algebraMap A K a))) i = _
  rw [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Module.Basis.baseChange_repr_tmul]
  simp only [Algebra.smul_def, mul_one]

omit [IsDomain A] in
/-- A finite ordinary basis supplies the generic differential dimension over the same base. -/
theorem finrank_fraction_of_basis [Fintype ι]
    (b : Module.Basis ι A (KaehlerDifferential Λ A)) :
    Module.finrank K (KaehlerDifferential Λ K) = Fintype.card ι :=
  Module.finrank_eq_card_basis (fractionBasis (K := K) b)

omit [IsDomain A] in
/-- Nonzero differentials survive the actual fraction localization over the unchanged base. -/
theorem fraction_D_ne_zero_of_basis (b : Module.Basis ι A (KaehlerDifferential Λ A))
    (a : A) (ha : D Λ A a ≠ 0) : D Λ K (algebraMap A K a) ≠ 0 := by
  intro hz
  apply ha
  apply b.repr.injective
  ext i
  apply IsFractionRing.injective A K
  have hi := fractionBasis_repr_D (K := K) b a i
  simpa only [hz, map_zero, Finsupp.zero_apply] using hi.symm

omit [IsDomain A] [Field K] [Algebra A K] [Algebra Λ K]
  [IsScalarTower Λ A K] [IsFractionRing A K] in
/-- A finite ordinary basis gives finiteness of every actual raw exterior power. -/
theorem finite_exterior_of_basis [Finite ι]
    (b : Module.Basis ι A (KaehlerDifferential Λ A)) (n : ℕ) :
    Module.Finite A (⋀[A]^n (KaehlerDifferential Λ A)) := by
  let : Module.Finite A (KaehlerDifferential Λ A) := Module.Finite.of_basis b
  infer_instance

end UnchangedBase

end KaehlerDifferential
