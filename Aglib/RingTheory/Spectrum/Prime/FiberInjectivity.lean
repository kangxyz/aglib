/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Detecting injectivity on residue-field fibres over a reduced ring

A map from a free module over a reduced ring is injective if its original
scalar extension to every prime residue field is injective. Coordinates
of a kernel element belong to every prime ideal and hence vanish.
Consequently, a surjection from a finite free module is an isomorphism
when the two original fibre dimensions agree everywhere. These statements
retain independent module universes and require no Noetherian hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct Module

namespace LinearMap

variable {R M N : Type*} [CommRing R] [IsReduced R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Free R M]

/-- For a free source over a reduced ring, injectivity is detected by the original
scalar-extension maps to all prime residue fields. No finite generation is needed. -/
theorem injective_of_residueField_baseChange_injective (f : M →ₗ[R] N)
    (hf : ∀ p : PrimeSpectrum R, Function.Injective (f.baseChange p.asIdeal.ResidueField)) :
    Function.Injective f := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  let b := Module.Free.chooseBasis R M
  apply b.repr.injective
  rw [map_zero]
  ext i
  change b.repr x i = 0
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let p : PrimeSpectrum R := ⟨P, hP⟩
  have hz : (1 : P.ResidueField) ⊗ₜ[R] x = 0 := by
    apply hf p
    simp only [LinearMap.baseChange_tmul, hx, tmul_zero, map_zero]
  have hc := congrArg (fun z => (b.baseChange P.ResidueField).repr z i) hz
  have ha : algebraMap R P.ResidueField (b.repr x i) = 0 := by
    simpa only [Basis.baseChange_repr_tmul, map_zero, Finsupp.zero_apply,
      Algebra.smul_def, mul_one] using hc
  exact P.algebraMap_residueField_eq_zero.mp ha

/-- A surjection from a finite free module over a reduced ring is bijective when
the original source and target residue-field fibre dimensions agree everywhere. -/
theorem bijective_of_surjective_of_finrank_fiber_eq [Module.Finite R M]
    (f : M →ₗ[R] N) (hsurj : Function.Surjective f)
    (hdim : ∀ p : PrimeSpectrum R,
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) =
        finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] N)) :
    Function.Bijective f := by
  let : Module.Finite R N := Module.Finite.of_surjective f hsurj
  refine ⟨f.injective_of_residueField_baseChange_injective (fun p => ?_), hsurj⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdim p)).mpr
    (LinearMap.baseChange_surjective p.asIdeal.ResidueField hsurj)

end LinearMap
