/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphism
public import Mathlib.RingTheory.Trace.Basic

/-!
# Surjectivity of the Galois endomorphism map from a perfect trace

For a finite free integral closure in a finite Galois extension, surjectivity
of the trace pairing gives an explicit expression for every base-linear
endomorphism as a sum of multiplication followed by automorphisms. This is a
conditional intermediate result: proving the trace hypothesis from etaleness
is separate, and no branch-purity conclusion is asserted here.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace IsIntegralClosure

variable (A K L B : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]
  [Module.Free A B] [Module.Finite A B]

/-- The sum of the restricted Galois actions is the original finite-free trace. -/
theorem sum_galRestrict_eq_trace (x : B) :
    (∑ g : L ≃ₐ[K] L, galRestrict A K L B g x) =
      algebraMap A B (Algebra.trace A B x) := by
  let : IsDomain A := (IsFractionRing.injective A K).isDomain
  let : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  apply IsIntegralClosure.algebraMap_injective B A L
  simp only [map_sum, algebraMap_galRestrict_apply]
  calc
    (∑ g : L ≃ₐ[K] L, g ((algebraMap B L) x)) =
        algebraMap K L (Algebra.trace K L ((algebraMap B L) x)) := by
      convert (trace_eq_sum_automorphisms (K := K) (L := L)
        ((algebraMap B L) x)).symm using 1; congr 1; ext; simp
    _ = _ := by
      rw [Algebra.trace_localization A A⁰]
      simp only [← IsScalarTower.algebraMap_apply]

/-- A surjective trace pairing supplies explicit integral coefficients for all
endomorphisms. This hypothesis is not assumed in the final purity theorem. -/
theorem galoisEndomorphism_surjective_of_traceForm_surjective
    (htrace : Function.Surjective (Algebra.traceForm A B)) :
    Function.Surjective (galoisEndomorphism A K L B) := by
  classical
  let b := Module.Free.chooseBasis A B
  choose d hd using fun i => htrace (b.coord i)
  intro f
  refine ⟨fun g => ∑ i, f (b i) * galRestrict A K L B g (d i), ?_⟩
  ext x
  rw [galoisEndomorphism_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← map_mul, ← Finset.mul_sum, sum_galRestrict_eq_trace A K L B]
  have hcoord (i) : Algebra.trace A B (d i * x) = b.repr x i :=
    congrArg (fun q : Module.Dual A B => q x) (hd i)
  simp_rw [hcoord]
  have hf := congrArg f (b.sum_repr x)
  simp only [map_sum, map_smul] at hf
  simpa only [Algebra.smul_def, mul_comm] using hf

end IsIntegralClosure
