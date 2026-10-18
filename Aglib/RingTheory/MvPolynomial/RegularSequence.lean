/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors, kangxyz
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# The original polynomial variables form weakly regular sequences

A new variable is regular modulo the ideal spanned by any other variables.
Consequently every finite list of distinct original polynomial variables is
weakly regular over an arbitrary commutative coefficient ring, including the
zero ring. The coefficient ring and coordinate type have independent
universes; the coordinate type need not be finite.

The two proofs are selectively ported from the user-supplied Apache-2.0
archive `motivic-cohomology-complete-current742-source-m27-20261016T002808.167583Z.tar.gz`,
member `Motivic/RingTheory/MvPolynomial/RegularSequence.lean` inside its
`motivic-cohomology/` directory. That member's SHA-256 is
`e7c2874e7260e03067827da56d70f854b6db9e243971c1e9106786da4d2fb4dc`.
Only the native namespace and qualified original variable names are adapted.
Native `RingTheory.Sequence.IsWeaklyRegular.of_flat` supplies subsequent
flat transport; no second implementation of that operation is introduced.
-/

@[expose] public section
namespace MvPolynomial
open RingTheory.Sequence
variable {R : Type*} [CommRing R]

/-- A new original variable is regular modulo the ideal spanned by the other variables. -/
theorem isSMulRegular_quotient_span_X {I : Type*} (s : Set I) (i : I) (hi : i ∉ s) :
    IsSMulRegular (MvPolynomial I R ⧸ Ideal.span ((MvPolynomial.X : I → MvPolynomial I R) '' s))
      (MvPolynomial.X i : MvPolynomial I R) := by
  classical
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro p hp
  rw [smul_eq_mul, MvPolynomial.mem_ideal_span_X_image] at hp
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hm' : Finsupp.single i 1 + m ∈ (MvPolynomial.X i * p).support := by
    simpa only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul] using hm
  obtain ⟨j, hj, h⟩ := hp _ hm'
  refine ⟨j, hj, ?_⟩
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij.symm, zero_add] using h

/-- Every finite list of distinct original variables is weakly regular. -/
theorem isWeaklyRegular_X {I : Type*} (l : List I) (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial I R) (l.map (MvPolynomial.X : I → MvPolynomial I R)) := by
  constructor
  intro i hi
  have hi' : i < l.length := by simpa only [List.length_map] using hi
  have hnew : l[i] ∉ {j | j ∈ l.take i} := by
    intro h
    obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp h
    have hji : j = i := hl.getElem_inj.mp he
    omega
  have heq : Ideal.ofList ((l.map (MvPolynomial.X : I → MvPolynomial I R)).take i) =
      Ideal.span (MvPolynomial.X '' {j | j ∈ l.take i}) := by
    rw [← List.map_take]
    unfold Ideal.ofList
    congr 1
    ext p
    exact List.mem_map
  rw [heq, Ideal.smul_eq_mul, Ideal.mul_top, List.getElem_map]
  exact isSMulRegular_quotient_span_X _ _ hnew

end MvPolynomial
