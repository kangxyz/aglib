/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual residue parameters at an arbitrary prime

Finite algebra generators descend to generators of the prime quotient. A
transcendence basis can be chosen among these finitely many residue values, and
every chosen value has an actual original generator lift. Evaluating parameters
at these lifts has zero contraction of the selected prime. This construction
uses no separability hypothesis and no residue-field coefficient section.
-/

@[expose] public section

noncomputable section

universe u v w

namespace ResidueParameterBasis

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [Algebra k B]
variable {ι : Type w} (z : ι → B) (q : Ideal B) [q.IsPrime]

omit [q.IsPrime] in
/-- The actual images of the original generators generate the prime quotient. -/
theorem residue_adjoin_eq_top (hz : Algebra.adjoin k (Set.range z) = ⊤) :
    Algebra.adjoin k (Set.range (fun i => Ideal.Quotient.mk q (z i))) = ⊤ := by
  have heq : Algebra.adjoin k (Set.range (fun i => Ideal.Quotient.mk q (z i))) =
      (Algebra.adjoin k (Set.range z)).map (Ideal.Quotient.mkₐ k q) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  rw [heq, hz, Algebra.map_top]
  exact (AlgHom.range_eq_top (Ideal.Quotient.mkₐ k q)).2
    (Ideal.Quotient.mkₐ_surjective k q)

/-- Select a finite residue transcendence basis and actual source-generator
indices lifting each basis value. There is no separating-basis condition. -/
theorem exists_residue_basis [Finite ι]
    (hz : Algebra.adjoin k (Set.range z) = ⊤) :
    ∃ s : Set (B ⧸ q), s.Finite ∧ ∃ t : s → ι,
      (∀ a, Ideal.Quotient.mk q (z (t a)) = (a : B ⧸ q)) ∧
      IsTranscendenceBasis k ((↑) : s → B ⧸ q) := by
  classical
  let r : ι → B ⧸ q := fun i => Ideal.Quotient.mk q (z i)
  have hr : Algebra.adjoin k (Set.range r) = ⊤ := residue_adjoin_eq_top z q hz
  let : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range r)) (B ⧸ q) := by
    constructor
    intro x
    have hx : x ∈ Algebra.adjoin k (Set.range r) := by rw [hr]; trivial
    exact isAlgebraic_algebraMap (A := B ⧸ q)
      (⟨x, hx⟩ : Algebra.adjoin k (Set.range r))
  obtain ⟨s, hs, hbase⟩ := exists_isTranscendenceBasis_subset (R := k) (Set.range r)
  refine ⟨s, (Set.finite_range r).subset hs,
    (fun a => Classical.choose (hs a.property)), ?_, hbase⟩
  intro a
  exact Classical.choose_spec (hs a.property)

variable {σ : Type*} (t : σ → B)

/-- Actual evaluation at chosen source parameters. -/
def parameterMap : MvPolynomial σ k →ₐ[k] B := MvPolynomial.aeval t

omit [q.IsPrime] in
/-- Algebraic independence in the residue domain gives zero prime contraction. -/
theorem parameterMap_comap_eq_bot
    (ht : AlgebraicIndependent k (fun i => Ideal.Quotient.mk q (t i))) :
    q.comap (parameterMap (k := k) t).toRingHom = ⊥ := by
  ext p
  change parameterMap (k := k) t p ∈ q ↔ p = 0
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have heval : Ideal.Quotient.mk q (parameterMap (k := k) t p) =
      MvPolynomial.aeval (fun i => Ideal.Quotient.mk q (t i)) p :=
    MvPolynomial.comp_aeval_apply t (Ideal.Quotient.mkₐ k q) p
  rw [heval]
  exact (algebraicIndependent_iff_injective_aeval.mp ht).eq_iff' (map_zero _)

omit [q.IsPrime] in
/-- Every nonzero parameter polynomial evaluates outside the selected prime. -/
theorem parameterMap_notMem
    (ht : AlgebraicIndependent k (fun i => Ideal.Quotient.mk q (t i)))
    {p : MvPolynomial σ k} (hp : p ≠ 0) : parameterMap (k := k) t p ∉ q := by
  intro h
  have hmem : p ∈ q.comap (parameterMap (k := k) t).toRingHom := h
  rw [parameterMap_comap_eq_bot q t ht] at hmem
  exact hp hmem

end ResidueParameterBasis
