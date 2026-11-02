/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Finite
public import Aglib.RingTheory.Nagata.FiniteTypeField
public import Aglib.RingTheory.Nagata.Polynomial
public import Aglib.RingTheory.NoetherNormalization.DimensionOne
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Nagata algebras of dimension at most one over a field

The actual Noether normalization has zero or one polynomial variables.
Japanese polynomial stability and finite ascent therefore prove the Japanese
property of every domain chart, without a perfection or separability premise.
Applying this to the actual prime quotients proves the Nagata property.
-/

@[expose] public noncomputable section

universe u

/-- Every finite-type domain of dimension at most one over an arbitrary field
is Japanese. The normalization and the tested finite extension are actual
algebras with their specified scalar actions. -/
theorem IsJapaneseRing.of_finiteType_field_dimLE_one
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hdim : ringKrullDim A ≤ 1) :
    IsJapaneseRing.{u, 0} A := by
  obtain ⟨n, hn, g, hg, hint⟩ :=
    NoetherNormalization.exists_integral_inj_algHom_dim_le_one k A hdim
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := g.toRingHom.toAlgebra
  let : IsScalarTower k P A :=
    IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  let : Algebra.FiniteType P A := Algebra.FiniteType.of_restrictScalars_finiteType k P A
  let : Algebra.IsIntegral P A := ⟨hint⟩
  let : Module.Finite P A := Algebra.IsIntegral.finite
  have hP : IsJapaneseRing.{u, 0} P := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
    · exact (IsJapaneseRing.of_field k).of_ringEquiv
        (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.toRingEquiv
    · exact (IsJapaneseRing.of_field k).polynomial.of_ringEquiv
        (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm.toRingEquiv
  exact hP.of_finite hg

/-- Finite-type algebras of dimension at most one over any field are Nagata.
The algebra need not be reduced or a domain. All tested extension fields have
the same ambient universe as the original rings. -/
theorem IsNagataRing.of_finiteType_field_dimLE_one
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (hdim : ringKrullDim A ≤ 1) :
    IsNagataRing.{u, 0} A := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine ⟨inferInstance, ?_⟩
  intro p hp
  exact IsJapaneseRing.of_finiteType_field_dimLE_one k (A ⧸ p)
    ((ringKrullDim_quotient_le p).trans hdim)
