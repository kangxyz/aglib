/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.IntegralModel
public import Aglib.RingTheory.DVRUniformizerBinomial
public import Aglib.RingTheory.LocalRing.SeparatedPrincipal
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # The original algebra adjoining a root of a DVR uniformizer

The literal `RootAlgebra n π` is a DVR at every positive exponent. Its original
root is a uniformizer, its residue field is unchanged, and it is the integral
closure in its actual fraction field. No separability, characteristic or
perfect-field hypothesis is used. This is the root-extension construction in
Stacks 09EV, not the tame subextension classification or Abhyankar's lemma.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace Algebra.Kummer

universe u v

section Quotient

variable {R : Type u} [CommRing R] (n : ℕ) (hn : 0 < n) (f : R)

/-- Killing the original adjoined root gives exactly the original parameter
quotient, through the actual coefficient and quotient maps. -/
def rootQuotientEquiv :
    (RootAlgebra n f ⧸ Ideal.span {AdjoinRoot.root (rootPolynomial n f)}) ≃ₐ[R]
      (R ⧸ Ideal.span {f}) := by
  let D := RootAlgebra n f
  let θ : D := AdjoinRoot.root (rootPolynomial n f)
  let J : Ideal D := Ideal.span {θ}
  let Q := D ⧸ J
  let B := R ⧸ Ideal.span {f}
  have hθ : algebraMap D Q θ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton θ))
  have hf : algebraMap R Q f = 0 := by
    rw [IsScalarTower.algebraMap_apply R D Q, ← root_pow n f, map_pow, hθ,
      zero_pow (Nat.ne_of_gt hn)]
  let α : D →ₐ[R] B := AdjoinRoot.liftAlgHom (rootPolynomial n f)
    (Algebra.ofId R B) 0 (by
      simp only [rootPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
        zero_pow (Nat.ne_of_gt hn), zero_sub, neg_eq_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f)))
  have hα : J ≤ RingHom.ker α.toRingHom := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  let α' : Q →ₐ[R] B := Ideal.Quotient.liftₐ J α (fun x hx => hα hx)
  let β : B →ₐ[R] Q := Ideal.Quotient.liftₐ (Ideal.span {f}) (Algebra.ofId R Q) (by
    intro x hx
    have h : Ideal.span {f} ≤ RingHom.ker (algebraMap R Q) :=
      Ideal.span_le.mpr (by
        intro a ha
        have ha' : a = f := Set.mem_singleton_iff.mp ha
        change algebraMap R Q a = 0
        exact (congrArg (algebraMap R Q) ha').trans hf)
    exact h hx)
  refine AlgEquiv.ofAlgHom α' β ?_ ?_
  · apply Ideal.Quotient.algHom_ext R
    apply AlgHom.ext
    intro r
    change α' (algebraMap R Q r) = algebraMap R B r
    exact α'.commutes r
  · apply Ideal.Quotient.algHom_ext R
    apply AdjoinRoot.algHom_ext
    change β (α θ) = algebraMap D Q θ
    have hαθ : α θ = 0 := AdjoinRoot.liftAlgHom_root _ _ _ _
    rw [hαθ, map_zero, hθ]

end Quotient

section DVR

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n)

include hn

local notation "D" => RootAlgebra n π
local notation "θ" => AdjoinRoot.root (rootPolynomial n π)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The literal root algebra is free over the original DVR. -/
theorem uniformizerRoot_free : Module.Free R D :=
  (monic_X_pow_sub_C π (Nat.ne_of_gt hn)).free_adjoinRoot

omit [IsDiscreteValuationRing R] in
/-- The original monic power basis has rank exactly the given exponent. -/
theorem uniformizerRoot_finrank : Module.finrank R D = n := by
  calc
    Module.finrank R D = (rootPolynomial n π).natDegree :=
      (AdjoinRoot.powerBasis' (monic_X_pow_sub_C π (Nat.ne_of_gt hn))).finrank
    _ = n := natDegree_X_pow_sub_C

include hπ in
/-- Eisenstein irreducibility makes the unchanged root algebra a domain. -/
theorem uniformizerRoot_isDomain : IsDomain D :=
  AdjoinRoot.isDomain_of_prime
    (irreducible_iff_prime.mp (IsDiscreteValuationRing.uniformizer_binomial_irreducible hπ n hn))

/-- The actual quotient by the original root is the original residue field. -/
def uniformizerRoot_quotientEquivResidue :
    (D ⧸ Ideal.span {θ}) ≃ₐ[R] ResidueField R :=
  (rootQuotientEquiv n hn π).trans
    (Ideal.quotientEquivAlgOfEq R hπ.maximalIdeal_eq.symm)

include hπ in
/-- The root generates a maximal ideal, by the actual residue-field comparison. -/
theorem uniformizerRoot_span_isMaximal : (Ideal.span {θ} : Ideal D).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    ((uniformizerRoot_quotientEquivResidue R π hπ n hn).toRingEquiv.isField
      (Field.toIsField (ResidueField R)))

include hπ in
/-- Every maximal ideal contains the original root: its power is the image of
the base uniformizer. Thus the literal algebra is local without henselianity. -/
theorem uniformizerRoot_isLocalRing : IsLocalRing D := by
  let : Module.Finite R D := root_finite n hn π
  have hJ := uniformizerRoot_span_isMaximal R π hπ n hn
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨Ideal.span {θ}, hJ, ?_⟩
  intro m hm
  let : m.IsMaximal := hm
  have hmunder : m.under R = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal m)
  have hπmem : algebraMap R D π ∈ m := by
    change π ∈ m.under R
    rw [hmunder, hπ.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton π)
  have hθmem : θ ∈ m := by
    apply (inferInstance : m.IsPrime).mem_of_pow_mem n
    rwa [root_pow]
  have hJm : (Ideal.span {θ} : Ideal D) ≤ m :=
    Ideal.span_le.mpr (by
      intro x hx
      have hx' : x = θ := Set.mem_singleton_iff.mp hx
      subst x
      exact hθmem)
  exact (hJ.eq_of_le hm.ne_top hJm).symm

include hπ in
/-- The original root, not merely an associated replacement, generates the maximal ideal. -/
theorem uniformizerRoot_maximalIdeal :
    letI := uniformizerRoot_isLocalRing R π hπ n hn
    maximalIdeal D = Ideal.span {θ} := by
  let := uniformizerRoot_isLocalRing R π hπ n hn
  exact (IsLocalRing.eq_maximalIdeal (uniformizerRoot_span_isMaximal R π hπ n hn)).symm

include hπ in
/-- The original root is nonzero, by its power equation and the faithful monic basis. -/
theorem uniformizerRoot_root_ne_zero : θ ≠ 0 := by
  let := uniformizerRoot_isDomain R π hπ n hn
  let : Module.Free R D := uniformizerRoot_free R π n hn
  intro hzero
  have hmap : algebraMap R D π = 0 := by
    rw [← root_pow n π, hzero, zero_pow (Nat.ne_of_gt hn)]
  exact hπ.ne_zero (FaithfulSMul.algebraMap_injective R D (hmap.trans (map_zero _).symm))

include hπ in
/-- The literal uniformizer root algebra is a DVR at every positive exponent. -/
theorem uniformizerRoot_isDiscreteValuationRing :
    letI := uniformizerRoot_isDomain R π hπ n hn
    IsDiscreteValuationRing D := by
  let := uniformizerRoot_isDomain R π hπ n hn
  let := uniformizerRoot_isLocalRing R π hπ n hn
  let : Module.Finite R D := root_finite n hn π
  let : IsNoetherianRing D := IsNoetherianRing.of_finite R D
  have hθ := uniformizerRoot_root_ne_zero R π hπ n hn
  exact IsLocalRing.isDiscreteValuationRing_of_isHausdorff_of_maximalIdeal_eq_span θ
    (uniformizerRoot_maximalIdeal R π hπ n hn) (fun m => pow_ne_zero m hθ)

include hπ in
/-- The original adjoined root is an actual uniformizer of the constructed DVR. -/
theorem uniformizerRoot_irreducible : Irreducible θ := by
  let := uniformizerRoot_isDomain R π hπ n hn
  let := uniformizerRoot_isDiscreteValuationRing R π hπ n hn
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal θ
  · exact uniformizerRoot_root_ne_zero R π hπ n hn
  · exact uniformizerRoot_maximalIdeal R π hπ n hn

include hπ in
/-- The same original root algebra is the integral closure of the original DVR
in any specified actual fraction field of that algebra. -/
theorem uniformizerRoot_isIntegralClosure (L : Type v) [Field L]
    [Algebra D L] [IsFractionRing D L] [Algebra R L] [IsScalarTower R D L] :
    IsIntegralClosure D R L := by
  let := uniformizerRoot_isDomain R π hπ n hn
  let := uniformizerRoot_isDiscreteValuationRing R π hπ n hn
  let : Module.Finite R D := root_finite n hn π
  refine ⟨IsFractionRing.injective D L, ?_⟩
  intro x
  constructor
  · intro hx
    exact IsIntegrallyClosed.algebraMap_eq_of_integral (hx.tower_top : IsIntegral D x)
  · rintro ⟨d, rfl⟩
    exact (_root_.IsIntegral.of_finite R d).map (IsScalarTower.toAlgHom R D L)

end DVR

end Algebra.Kummer
