/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.KrullDimension.Polynomial
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Properties

/-! Actual spectrum-stalk forms of the finite polynomial algebra results. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- Regularity of the actual polynomial-scheme stalk. -/
theorem polynomial_spec_stalk_isRegularLocalRing
    (K : Type u) [Field K] (n : ℕ)
    (x : Spec (.of (MvPolynomial (Fin n) K))) :
    IsRegularLocalRing ((Spec (.of (MvPolynomial (Fin n) K))).presheaf.stalk x) := by
  let : x.asIdeal.IsPrime := x.2
  let e := (Spec.stalkIso (.of (MvPolynomial (Fin n) K)) x).commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-- Dimension at every polynomial-scheme point is at most n. -/
theorem polynomial_spec_stalk_dimension_le
    (K : Type u) [Field K] (n : ℕ)
    (x : Spec (.of (MvPolynomial (Fin n) K))) :
    ringKrullDim ((Spec (.of (MvPolynomial (Fin n) K))).presheaf.stalk x) ≤ n := by
  let : x.asIdeal.IsPrime := x.2
  let e := (Spec.stalkIso (.of (MvPolynomial (Fin n) K)) x).commRingCatIsoToRingEquiv
  rw [ringKrullDim_eq_of_ringEquiv e]
  simpa using MvPolynomial.mvPolynomial_localizationAtPrime_dimension_le K (Fin n) x.asIdeal

/-- Exact polynomial-scheme stalk dimension at maximal points. -/
theorem polynomial_spec_stalk_dimension_of_isMaximal
    (K : Type u) [Field K] (n : ℕ)
    (x : Spec (.of (MvPolynomial (Fin n) K))) [x.asIdeal.IsMaximal] :
    ringKrullDim ((Spec (.of (MvPolynomial (Fin n) K))).presheaf.stalk x) = n := by
  let e := (Spec.stalkIso (.of (MvPolynomial (Fin n) K)) x).commRingCatIsoToRingEquiv
  rw [ringKrullDim_eq_of_ringEquiv e]
  simpa using MvPolynomial.mvPolynomial_localizationAtPrime_dimension_of_isMaximal
    K (Fin n) x.asIdeal

/-- Etale polynomial coordinates take maximal points of the chart to maximal
polynomial points. Only integrality of the finite field residue is used. -/
theorem isMaximal_comap_etale_polynomial
    (K : Type u) [Field K] (n : ℕ) {B : Type u} [CommRing B]
    (g : MvPolynomial (Fin n) K →+* B) (hg : g.Etale)
    (q : Ideal B) [q.IsMaximal] : (q.comap g).IsMaximal := by
  let A := MvPolynomial (Fin n) K
  let : Algebra A B := g.toAlgebra
  have : Algebra.Etale A B := hg
  let : Algebra K B := (g.comp MvPolynomial.C).toAlgebra
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FiniteType K B :=
    Algebra.FiniteType.trans (R := K) (S := A) (A := B) inferInstance inferInstance
  let g' : A →ₐ[K] B := { toRingHom := g, commutes' := fun _ => rfl }
  exact Ideal.isMaximal_comap_of_finiteType_field K g' q

end AlgebraicGeometry.Scheme
