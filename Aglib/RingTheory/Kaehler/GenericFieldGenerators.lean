/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.GenericParameter
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-! # Original field generators after adjoining generic parameters

The actual coefficient images generate the enlarged fraction field over the
canonical generic parameter field. Neither family of indices need be finite.
-/

@[expose] public noncomputable section

namespace GenericParameterField

attribute [local instance] MvPolynomial.algebraMvPolynomial fractionAlgebra

variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable (ι : Type*) {σ : Type*}

local notation "P" => MvPolynomial ι k
local notation "B" => MvPolynomial ι K
local notation "F" => FractionRing P
local notation "L" => FractionRing B

/-- Actual original field generators still generate after adjoining the same
independent parameters to the ground field and the coefficient field. -/
theorem adjoin_coefficient_generators_eq_top (x : σ → K)
    (hx : IntermediateField.adjoin k (Set.range x) = ⊤) :
    IntermediateField.adjoin F (Set.range (fun i => algebraMap K L (x i))) = ⊤ := by
  let H := IntermediateField.adjoin F (Set.range (fun i => algebraMap K L (x i)))
  have hcoeff (a : K) : algebraMap K L a ∈ H := by
    have ha : a ∈ IntermediateField.adjoin k (Set.range x) := by
      rw [hx]
      trivial
    refine IntermediateField.adjoin_induction («F» := k)
      (p := fun a _ => algebraMap K L a ∈ H) ?_ ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    · intro c
      rw [← IsScalarTower.algebraMap_apply k K L,
        IsScalarTower.algebraMap_apply k F L]
      exact H.algebraMap_mem _
    · intro a b _ _ ha hb
      rw [map_add]
      exact H.add_mem ha hb
    · intro a _ ha
      rw [map_inv₀]
      exact H.inv_mem ha
    · intro a b _ _ ha hb
      rw [map_mul]
      exact H.mul_mem ha hb
  have hvar (i : ι) : algebraMap B L (MvPolynomial.X i) ∈ H := by
    rw [← fractionMap_X k K ι i]
    exact H.algebraMap_mem _
  have hpoly (f : B) : algebraMap B L f ∈ H := by
    induction f using MvPolynomial.induction_on with
    | C c =>
        change algebraMap B L (algebraMap K B c) ∈ H
        rw [← IsScalarTower.algebraMap_apply K B L]
        exact hcoeff c
    | add f g hf hg =>
        rw [map_add]
        exact H.add_mem hf hg
    | mul_X f i hf =>
        rw [map_mul]
        exact H.mul_mem hf (hvar i)
  apply top_unique
  intro z _
  obtain ⟨f, g, _, rfl⟩ := IsFractionRing.div_surjective B z
  exact H.div_mem (hpoly f) (hpoly g)

end GenericParameterField
