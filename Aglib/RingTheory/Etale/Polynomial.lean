/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Maximal ideals in etale polynomial algebras

For the original etale ring map out of a finite polynomial algebra over a
field, the comap of a maximal ideal is maximal. The field and coefficient
algebra retain their original common universe; separability and a scheme
structure are not assumptions.

Source: Aglib/AlgebraicGeometry/Stalk/Polynomial.lean:51–65 at
451aeda6b8bb5b44402b574dd6cf60f912360f8c. Only the approved native owner/name changes.
-/

@[expose] public section

universe u

namespace RingHom.Etale

/-- Etale polynomial coordinates take maximal points of the chart to maximal
polynomial points. Only integrality of the finite field residue is used. -/
theorem isMaximal_comap_polynomial
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

end RingHom.Etale
