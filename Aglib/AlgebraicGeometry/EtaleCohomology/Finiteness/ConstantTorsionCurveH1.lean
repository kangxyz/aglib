/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ConstantPrimaryModules
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PrimeToCharacteristicCurveModules
public import Aglib.Algebra.Module.FiniteTorsion

/-!
# Finite original H1 for constant torsion modules on curves

The characteristic and invertible-prime theorems cover every prime. Strong
induction on a positive annihilator then uses the actual kernel of scalar
multiplication and its actual quotient. Finite generation is over the original
Noetherian coefficient ring, not over the integers or a prime field, and the
underlying coefficient group need not be finite. Only degree one is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness

universe u e l

attribute [local instance] hasSheafifyLarge

variable {k : Type u} [Field k] [IsSepClosed k] (X : FScheme k) (hX : Properties X)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X.left)]
  [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{e}]
  (Λ : Type l) [CommRing Λ]

include hX

/-- A finite literal module killed by any prime has finite original constant H1
on a smooth proper geometrically connected curve. No Noetherian hypothesis or
restriction on the prime relative to the characteristic is required. -/
theorem constantModule_h1_finite_of_prime_annihilator
    (p : ℕ) [Fact p.Prime] (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, p • x = 0) :
    Module.Finite Λ ((ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology Λ 1).obj M) := by
  by_cases hp : (p : k) = 0
  · let : IsProper X.hom := hX.proper
    let : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    exact constantModule_cohomology_finite_of_prime_nsmul X p Λ 1 M hM
  · exact constantModule_h1_finite_of_prime_nsmul X hX p (isUnit_iff_ne_zero.mpr hp) Λ M hM

/-- A finite literal module with any positive additive annihilator has finite
original constant H1 over its original Noetherian coefficient ring. -/
theorem constantModule_h1_finite_of_pos_nsmul [IsNoetherianRing Λ]
    (n : ℕ) (hn : 0 < n) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, n • x = 0) :
    Module.Finite Λ ((ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology Λ 1).obj M) := by
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      let : Subsingleton M := subsingleton_of_forall_eq 0 (fun x => by
        simpa only [one_nsmul] using hM x)
      let : Subsingleton
          ((ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology Λ 1).obj M) :=
        ModuleCat.subsingleton_of_isZero
          ((ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology Λ 1).map_isZero
            (ModuleCat.isZero_of_subsingleton M))
      infer_instance
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      let : Fact p.Prime := ⟨hp⟩
      have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
      have hlt : n / p < n := Nat.div_lt_self hn hp.one_lt
      let N : Submodule Λ M := LinearMap.ker ((n / p) • (LinearMap.id : M →ₗ[Λ] M))
      have hN : ∀ x : N, (n / p) • x = 0 := by
        intro x
        apply Subtype.ext
        exact x.property
      have hQ : ∀ x : M ⧸ N, p • x = 0 := by
        intro x
        obtain ⟨m, rfl⟩ := N.mkQ_surjective x
        rw [← map_nsmul]
        apply (Submodule.Quotient.mk_eq_zero N).mpr
        change (n / p) • (p • m) = 0
        rw [← mul_nsmul, Nat.mul_div_cancel' hpn]
        exact hM m
      let S := ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
        (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero
      have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
        (LinearMap.exact_subtype_mkQ N) N.subtype_injective N.mkQ_surjective
      let : Module.Finite Λ
          ((ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology Λ 1).obj S.X₁) :=
        ih (n / p) hlt hm (ModuleCat.of Λ N) hN
      let : Module.Finite Λ
          ((ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology Λ 1).obj S.X₃) :=
        constantModule_h1_finite_of_prime_annihilator X hX Λ p (ModuleCat.of Λ (M ⧸ N)) hQ
      exact ModuleCat.Sheaf.finite_constantCohomology_of_shortExact
        X.left.smallEtaleTopology Λ S hS 1

/-- Elementwise additive torsion suffices for a finite module: finite generation
over the original coefficient ring supplies the positive uniform annihilator. -/
theorem constantModule_h1_finite_of_isAddTorsion [IsNoetherianRing Λ]
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] (hM : IsAddTorsion M) :
    Module.Finite Λ ((ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology Λ 1).obj M) := by
  obtain ⟨n, hn, hzero⟩ := Module.Finite.exists_pos_nsmul_eq_zero_of_isAddTorsion Λ hM
  exact constantModule_h1_finite_of_pos_nsmul X hX Λ n hn M hzero

end AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness
