/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Spectrum.Prime.Surjectivity
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Topology.Semicontinuity.Defs

/-!
# Upper semicontinuity of finite-module fibre dimensions

The dimension of the original residue-field fibre of a finite module is
upper semicontinuous on the prime spectrum of any commutative ring. A basis
chosen from the spanning original elements `1 ⊗ m` lifts to a finite free
module mapping to the original module. Its fibre map is surjective on an
actual basic open neighbourhood, giving the dimension bound there.
No finite presentation, flatness or Noetherianity is required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct Module Set Topology

namespace Module

universe u v

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M]

/-- Every point has a basic neighbourhood on which the actual fibre dimension is at most
its value at that point. The original module need only be finite. -/
theorem exists_basicOpen_finrank_fiber_le (p : PrimeSpectrum R) :
    ∃ r ∉ p.asIdeal, ∀ q ∈ PrimeSpectrum.basicOpen r,
      finrank q.asIdeal.ResidueField (q.asIdeal.Fiber M) ≤
        finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) := by
  classical
  let K := p.asIdeal.ResidueField
  let V := K ⊗[R] M
  let s : Set V := Set.range (TensorProduct.mk R K M 1)
  have hs : ⊤ ≤ Submodule.span K s := by
    simpa only [Submodule.baseChange_top, Submodule.map_top, LinearMap.coe_range, s] using
      (Submodule.baseChange_eq_span K (⊤ : Submodule R M)).le
  have hlocal {I : Type (max u v)} (b : Basis I K V) (hb : Set.range b ⊆ s) :
      ∃ r ∉ p.asIdeal, ∀ q ∈ PrimeSpectrum.basicOpen r,
        finrank q.asIdeal.ResidueField (q.asIdeal.Fiber M) ≤ finrank K V := by
    let : Finite I := Module.Finite.finite_basis b
    let : Fintype I := Fintype.ofFinite I
    have hlift : ∀ i : I, ∃ m : M, (1 : K) ⊗ₜ[R] m = b i :=
      fun i => hb ⟨i, rfl⟩
    choose m hm using hlift
    let π : (I →₀ R) →ₗ[R] M := Finsupp.linearCombination R m
    have hπ : Function.Surjective (π.baseChange K) := by
      rw [← LinearMap.range_eq_top]
      apply top_unique
      rw [← b.span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      refine ⟨(1 : K) ⊗ₜ[R] Finsupp.single i 1, ?_⟩
      simpa only [LinearMap.baseChange_tmul, π, Finsupp.linearCombination_single, one_smul]
        using hm i
    obtain ⟨r, hpr, hr⟩ :=
      LinearMap.exists_basicOpen_residueField_baseChange_surjective π p hπ
    refine ⟨r, hpr, fun q hq => ?_⟩
    have hd := LinearMap.finrank_le_finrank_of_surjective (hr q hq)
    let bR : Basis I R (I →₀ R) := Finsupp.basisSingleOne
    rw [Module.finrank_eq_card_basis (bR.baseChange q.asIdeal.ResidueField),
      ← Module.finrank_eq_card_basis b] at hd
    exact hd
  exact hlocal (Basis.ofSpan hs) (Basis.ofSpan_subset hs)

/-- The dimension of the original residue-field fibre of any finite module is upper
semicontinuous on the prime spectrum, with independent ring and module universes. -/
theorem upperSemicontinuous_finrank_fiber :
    UpperSemicontinuous (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M)) := by
  intro p n hn
  obtain ⟨r, hpr, hr⟩ := exists_basicOpen_finrank_fiber_le R M p
  filter_upwards [(PrimeSpectrum.basicOpen r).isOpen.mem_nhds hpr] with q hq
  exact (hr q hq).trans_lt hn

end Module
