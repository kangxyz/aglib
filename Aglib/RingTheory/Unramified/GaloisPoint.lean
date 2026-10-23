/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Finite Galois points of unramified algebras over a field

A nontrivial essentially finite-type formally unramified algebra has a maximal
ideal whose residue field is finite separable over the base. Embed that field
in the actual separable closure and take its native normal closure. This
constructs a point over a finite Galois extension, without any excellence,
perfectness, or algebraic-closedness assumption on the base field.
-/

@[expose] public noncomputable section

namespace Algebra.FormallyUnramified

/-- A nontrivial essentially finite-type formally unramified algebra over a
field has a point over a finite Galois intermediate field of its separable closure. -/
theorem exists_finiteGalois_algHom (K A : Type*) [Field K] [CommRing A]
    [Nontrivial A] [Algebra K A] [Algebra.EssFiniteType K A]
    [Algebra.FormallyUnramified K A] :
    ∃ L : FiniteGaloisIntermediateField K (SeparableClosure K), Nonempty (A →ₐ[K] L) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let Q := A ⧸ m
  let : Field Q := Ideal.Quotient.field m
  let : FiniteDimensional K Q := Algebra.FormallyUnramified.finite_of_free K Q
  let : Algebra.IsSeparable K Q := Algebra.FormallyUnramified.isSeparable K Q
  let e : Q →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let : Algebra Q (SeparableClosure K) := e.toRingHom.toAlgebra
  let : IsScalarTower K Q (SeparableClosure K) := IsScalarTower.of_algHom e
  let L : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := IntermediateField.normalClosure K Q (SeparableClosure K) }
  exact ⟨L, ⟨(IsScalarTower.toAlgHom K Q L).comp (Ideal.Quotient.mkₐ K m)⟩⟩

end Algebra.FormallyUnramified
