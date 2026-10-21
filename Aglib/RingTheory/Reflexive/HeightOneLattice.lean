/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.FractionLattice
public import Aglib.RingTheory.IntegralClosure.HeightOneIntersection

/-! A reflexive lattice over a normal Noetherian domain is recovered in codimension one. -/

@[expose] public section

noncomputable section

namespace Module

variable {R K M Mₖ : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module R M] [AddCommGroup Mₖ] [Module R Mₖ]
  [Module K Mₖ] [IsScalarTower R K Mₖ]
  [FinitePresentation R M] [FinitePresentation R (Dual R M)] [IsReflexive R M]

include K in
/-- A generic vector belongs to a reflexive lattice if its denominator can be cleared
outside every height-one prime. -/
theorem IsReflexive.mem_range_of_forall_height_one (f : M →ₗ[R] Mₖ)
    [IsLocalizedModule (nonZeroDivisors R) f] (x : Mₖ)
    (hx : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      ∃ s ∉ p, s • x ∈ Set.range f) : x ∈ Set.range f := by
  apply IsReflexive.mem_range_of_dual (K := K) f x
  intro l
  apply IsIntegrallyClosed.mem_range_of_forall_height_one
  intro p hp hh
  obtain ⟨s, hs, m, hm⟩ := hx p hp hh
  refine ⟨s, hs, l m, ?_⟩
  let d := IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) f
    (Algebra.linearMap R K) K
  change algebraMap R K (l m) = d l x * algebraMap R K s
  calc
    algebraMap R K (l m) = d l (f m) :=
      (IsLocalizedModule.map_apply (nonZeroDivisors R) f (Algebra.linearMap R K) l m).symm
    _ = d l (s • x) := congrArg (d l) hm
    _ = d l x * algebraMap R K s := by
      simp only [LinearMap.map_smul_of_tower, Algebra.smul_def, mul_comm]

end Module
