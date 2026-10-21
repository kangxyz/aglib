/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Discriminant

/-!
# Trace pairings of finite algebras

The native algebra trace detects reducedness through its pairing. Over a field,
finite etale algebras have nondegenerate trace pairings, including the zero algebra.
These results are prerequisites for the finite-flat branch-purity criterion.
-/

@[expose] public section

noncomputable section

open Module

namespace Algebra

/-- The trace of a finite product is the sum of the traces of its components. -/
theorem trace_pi_apply {R ι : Type*} [CommRing R] [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)] (x : ∀ i, S i) :
    trace R (∀ i, S i) x = ∑ i, trace R (S i) (x i) := by
  classical
  let b := fun i ↦ Module.Free.chooseBasis R (S i)
  rw [trace_eq_matrix_trace (Pi.basis b)]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sigma, leftMulMatrix_eq_repr_mul,
    Pi.basis_repr, Pi.mul_apply, Pi.basis_apply, Pi.single_eq_same]
  congr 1
  funext i
  rw [trace_eq_matrix_trace (b i)]
  simp only [Matrix.trace, Matrix.diag, leftMulMatrix_eq_repr_mul]

/-- A nondegenerate trace pairing over a reduced ring rules out nilpotents. -/
theorem isReduced_of_traceForm_nondegenerate {R S : Type*}
    [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    (h : (traceForm R S).Nondegenerate) : IsReduced S := by
  refine ⟨fun x hx ↦ h.1 x fun y ↦ ?_⟩
  exact (isNilpotent_trace_of_isNilpotent ((Commute.all x y).isNilpotent_mul_right hx)).eq_zero

/-- An algebra equivalence preserves nondegeneracy of the trace pairing. -/
theorem traceForm_nondegenerate_of_algEquiv {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) (h : (traceForm R S).Nondegenerate) :
    (traceForm R T).Nondegenerate := by
  constructor
  · intro x hx
    apply e.symm.injective
    rw [map_zero]
    apply h.1
    intro y
    change trace R S (e.symm x * y) = 0
    rw [← trace_eq_of_algEquiv e, map_mul, e.apply_symm_apply]
    exact hx (e y)
  · intro y hy
    apply e.symm.injective
    rw [map_zero]
    apply h.2
    intro x
    change trace R S (x * e.symm y) = 0
    rw [← trace_eq_of_algEquiv e, map_mul, e.apply_symm_apply]
    exact hy (e x)

/-- Nondegeneracy of the trace pairing is unchanged by an algebra equivalence. -/
theorem traceForm_nondegenerate_iff_of_algEquiv {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) :
    (traceForm R S).Nondegenerate ↔ (traceForm R T).Nondegenerate :=
  ⟨traceForm_nondegenerate_of_algEquiv e, traceForm_nondegenerate_of_algEquiv e.symm⟩

/-- Pairing against one component of a product only sees that component. -/
theorem traceForm_pi_single_right {R ι : Type*} [CommRing R] [Finite ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)]
    [DecidableEq ι] (x : ∀ i, S i) (i : ι) (y : S i) :
    traceForm R (∀ i, S i) x (Pi.single i y) = traceForm R (S i) (x i) y := by
  let := Fintype.ofFinite ι
  rw [traceForm_apply, trace_pi_apply, Finset.sum_eq_single i]
  · simp only [Pi.mul_apply, Pi.single_eq_same, traceForm_apply]
  · intro j _ hji
    simp [hji]
  · simp

/-- A product trace pairing is nondegenerate exactly when each component is. -/
theorem traceForm_pi_nondegenerate_iff {R ι : Type*} [CommRing R] [Finite ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)] :
    (traceForm R (∀ i, S i)).Nondegenerate ↔
      ∀ i, (traceForm R (S i)).Nondegenerate := by
  classical
  constructor
  · intro h i
    have hleft : (traceForm R (S i)).SeparatingLeft := by
      intro x hx
      have hz := h.1 (Pi.single i x) fun y ↦ by
        rw [(traceForm_isSymm R).eq, traceForm_pi_single_right]
        exact ((traceForm_isSymm R).eq _ _).trans (hx (y i))
      simpa using congrArg (fun z ↦ z i) hz
    exact ⟨hleft, fun x hx ↦ hleft x fun y ↦
      ((traceForm_isSymm R).eq _ _).trans (hx y)⟩
  · intro h
    have hleft : (traceForm R (∀ i, S i)).SeparatingLeft := by
      intro x hx
      funext i
      apply (h i).1
      intro y
      rw [← traceForm_pi_single_right S x i y]
      exact hx _
    exact ⟨hleft, fun x hx ↦ hleft x fun y ↦
      ((traceForm_isSymm R).eq _ _).trans (hx y)⟩

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
/-- A finite algebra over a field is etale exactly when its trace pairing is
nondegenerate. The statement allows the zero algebra. -/
theorem etale_iff_traceForm_nondegenerate {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Module.Finite K A] :
    Etale K A ↔ (traceForm K A).Nondegenerate := by
  classical
  constructor
  · intro h
    obtain ⟨I, _, F, _, _, e, hF⟩ := (Etale.iff_exists_algEquiv_prod K A).mp h
    let := Fintype.ofFinite I
    have (i : I) : Module.Finite K (F i) := (hF i).1
    have (i : I) : Algebra.IsSeparable K (F i) := (hF i).2
    apply traceForm_nondegenerate_of_algEquiv e.symm
    exact (traceForm_pi_nondegenerate_iff F).mpr fun i ↦ traceForm_nondegenerate K (F i)
  · intro h
    let : IsReduced A := isReduced_of_traceForm_nondegenerate h
    let : IsArtinianRing A := .of_finite K A
    let e := (IsArtinianRing.equivPi A).restrictScalars K
    have hp := (traceForm_pi_nondegenerate_iff
      (fun i : MaximalSpectrum A ↦ A ⧸ i.asIdeal)).mp
      (traceForm_nondegenerate_of_algEquiv e h)
    apply (Etale.iff_exists_algEquiv_prod K A).mpr
    refine ⟨MaximalSpectrum A, inferInstance, (fun i ↦ A ⧸ i.asIdeal),
      inferInstance, inferInstance, e, fun i ↦ ⟨inferInstance, ?_⟩⟩
    exact ((traceForm_nondegenerate_tfae K (A ⧸ i.asIdeal)).out 3 1).mp (hp i)

end Algebra
