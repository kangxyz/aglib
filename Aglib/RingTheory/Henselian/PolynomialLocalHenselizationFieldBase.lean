/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationPrecision
public import Aglib.RingTheory.Henselian.HenselizationNoetherian
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# The actual zero-variable base over a field

The original formal map is injective by faithful flatness of the actual
henselization-to-completion map. Over a field and with no polynomial variables,
the formal target has zero maximal ideal, so finite-quotient surjectivity is
actual surjectivity. This proves the base case on the original map. It asserts
no corresponding isomorphism for an excellent DVR and its completion.
-/

@[expose] public section

namespace PolynomialLocalHenselization

/-- The original formal map is injective, not only its finite-quotient approximations. -/
theorem toFormalSeries_injective (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (n : ℕ) : Function.Injective (toFormalSeries R n) := by
  let L := PolynomialLocalRing R n
  let H := Henselization L
  let S := AdicCompletion (IsLocalRing.maximalIdeal L) L
  let : Algebra H S := (Henselization.toAdicCompletion L).toRingHom.toAlgebra
  let : Module.FaithfullyFlat H S := Henselization.faithfullyFlat_toAdicCompletion L
  have hinj : Function.Injective (Henselization.toAdicCompletion L) :=
    FaithfulSMul.algebraMap_injective H S
  intro x y h
  apply hinj
  apply (PolynomialLocalRing.completionEquiv R n).injective
  change completionFormalMap R n x = completionFormalMap R n y
  rw [completionFormalMap_eq_toFormalSeries]
  exact h

/-- The actual no-variable formal target over a field has zero maximal ideal. -/
theorem maximalIdeal_formalSeries_zero (k : Type*) [Field k] :
    IsLocalRing.maximalIdeal (PolynomialLocalRing.FormalSeries k 0) = ⊥ := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let ec : k ≃ₐ[k] AdicCompletion (IsLocalRing.maximalIdeal k) k :=
    AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal k)
  let e : PolynomialLocalRing.FormalSeries k 0 ≃+* k :=
    (MvPowerSeries.isEmptyEquiv (Fin 0)
      (AdicCompletion (IsLocalRing.maximalIdeal k) k)).toRingEquiv.trans
      ec.symm.toRingEquiv
  apply (Ideal.map_eq_bot_iff_of_injective e.injective).mp
  rw [IsLocalRing.map_ringEquiv_maximalIdeal, IsLocalRing.maximalIdeal_eq_bot]

/-- Zero-variable approximation over a field is an isomorphism of the original maps. -/
theorem toFormalSeries_zero_bijective (k : Type*) [Field k] :
    Function.Bijective (toFormalSeries k 0) := by
  refine ⟨toFormalSeries_injective k 0, ?_⟩
  intro b
  obtain ⟨a, ha⟩ := quotient_mk_comp_toFormalSeries_surjective k 0 1
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PolynomialLocalRing.FormalSeries k 0) ^ 1) b)
  change Ideal.Quotient.mk _ (toFormalSeries k 0 a) = Ideal.Quotient.mk _ b at ha
  have h := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ha
  rw [maximalIdeal_formalSeries_zero, pow_one, Ideal.mem_bot, sub_eq_zero] at h
  exact ⟨a, h⟩

/-- The zero-variable equivalence has precisely the original formal map as its forward map. -/
noncomputable def zeroFormalEquiv (k : Type*) [Field k] :
    PolynomialLocalHenselization k 0 ≃ₐ[k] PolynomialLocalRing.FormalSeries k 0 :=
  AlgEquiv.ofBijective (toFormalSeries k 0) (toFormalSeries_zero_bijective k)

@[simp] theorem zeroFormalEquiv_apply (k : Type*) [Field k]
    (a : PolynomialLocalHenselization k 0) : zeroFormalEquiv k a = toFormalSeries k 0 a := rfl

/-- The base case lifts an arbitrary formal solution exactly through the original map. -/
theorem exists_exact_solution_zero_variables (k : Type*) [Field k] {σ ι : Type*}
    (F : ι → MvPolynomial σ (PolynomialLocalHenselization k 0))
    (y : σ → PolynomialLocalRing.FormalSeries k 0)
    (hF : ∀ i, MvPolynomial.eval₂Hom (toFormalSeries k 0).toRingHom y (F i) = 0) :
    ∃ y₀ : σ → PolynomialLocalHenselization k 0,
      (∀ i, MvPolynomial.eval y₀ (F i) = 0) ∧
      ∀ j, toFormalSeries k 0 (y₀ j) = y j := by
  let y₀ := fun j ↦ (zeroFormalEquiv k).symm (y j)
  have hy : (fun j ↦ toFormalSeries k 0 (y₀ j)) = y := by
    funext j
    exact (zeroFormalEquiv k).apply_symm_apply (y j)
  refine ⟨y₀, ?_, fun j ↦ congrFun hy j⟩
  intro i
  apply toFormalSeries_injective k 0
  change (toFormalSeries k 0).toRingHom (MvPolynomial.eval y₀ (F i)) =
    (toFormalSeries k 0).toRingHom 0
  rw [map_zero, MvPolynomial.eval₂_comp]
  change MvPolynomial.eval₂Hom (toFormalSeries k 0).toRingHom
    (fun j ↦ toFormalSeries k 0 (y₀ j)) (F i) = 0
  rw [hy]
  exact hF i

end PolynomialLocalHenselization
