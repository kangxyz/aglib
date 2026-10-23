/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Associated primes under flat base change of a finite module

The actual local scalar-extension maps give contraction of associated
primes. A finite prime filtration then locates each associated prime of
the tensor product in the original prime-quotient fiber. Noetherianity is
required only for the base ring; the input module is finite.
-/

@[expose] public section

open scoped TensorProduct

/-- A finite module over a Noetherian local ring has associated maximal
ideal if its actual flat local scalar extension has associated maximal
ideal. No Noetherianity of the target ring is assumed. -/
theorem IsAssociatedPrime.maximalIdeal_of_isBaseChange_of_flat_local
    {R S M N : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) (hf : IsBaseChange S f)
    (h : IsAssociatedPrime (IsLocalRing.maximalIdeal S) N) :
    IsAssociatedPrime (IsLocalRing.maximalIdeal R) M := by
  classical
  by_contra hnot
  have hcover : ¬ ((IsLocalRing.maximalIdeal R : Set R) ⊆
      ⋃ p ∈ associatedPrimes R M, (p : Set R)) := by
    intro hsub
    obtain ⟨p, hp, hmp⟩ :=
      (Ideal.subset_union_prime_finite (associatedPrimes.finite R M)
        (I := IsLocalRing.maximalIdeal R) (f := id) (0 : Ideal R) (0 : Ideal R)
        (fun _ hp _ _ => hp.isPrime)).mp hsub
    have heq : p = IsLocalRing.maximalIdeal R :=
      le_antisymm (IsLocalRing.le_maximalIdeal hp.isPrime.ne_top) hmp
    exact hnot (heq ▸ hp)
  obtain ⟨a, ham, ha⟩ := Set.not_subset.mp hcover
  rw [biUnion_associatedPrimes_eq_compl_regular R M] at ha
  have hreg : IsSMulRegular M a := not_not.mp ha
  have hregN : IsSMulRegular N (algebraMap R S a) :=
    hreg.of_flat_of_isBaseChange hf
  have haS : algebraMap R S a ∈ IsLocalRing.maximalIdeal S := by
    change a ∈ (IsLocalRing.maximalIdeal S).comap (algebraMap R S)
    rw [IsLocalRing.maximalIdeal_comap]
    exact ham
  obtain ⟨y, hy⟩ := h.2
  have hy0 : y ≠ 0 := by
    intro hzero
    apply h.isPrime.ne_top
    rw [hzero, Submodule.colon_singleton_zero, Ideal.radical_top] at hy
    exact hy
  rw [hy, Ideal.mem_radical_iff] at haS
  obtain ⟨n, hn⟩ := haS
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hn
  exact hy0 ((IsSMulRegular.pow n hregN).right_eq_zero_of_smul hn)


/-- Contraction of an associated prime through a flat scalar extension
of a finite module over a Noetherian ring. The map is the original
coefficient map; the target ring need not be Noetherian or local. -/
theorem IsAssociatedPrime.comap_of_isBaseChange_of_flat
    {R S M N : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) (hf : IsBaseChange S f)
    {q : Ideal S} (hq : IsAssociatedPrime q N) :
    IsAssociatedPrime (q.comap (algebraMap R S)) M := by
  let : q.IsPrime := hq.isPrime
  let p : Ideal R := q.comap (algebraMap R S)
  let : p.IsPrime := inferInstance
  let A := Localization.AtPrime p
  let C := Localization.AtPrime q
  let Mp := LocalizedModule p.primeCompl M
  let Nq := LocalizedModule q.primeCompl N
  let i : M →ₗ[R] Mp := LocalizedModule.mkLinearMap p.primeCompl M
  let j : N →ₗ[S] Nq := LocalizedModule.mkLinearMap q.primeCompl N
  let e : A →+* C := Localization.localRingHom p q (algebraMap R S) rfl
  let : Algebra A C := e.toAlgebra
  let : IsLocalHom (algebraMap A C) :=
    Localization.isLocalHom_localRingHom p q (algebraMap R S) rfl
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R C r = e (algebraMap R A r)
    rw [show e (algebraMap R A r) = algebraMap S C (algebraMap R S r) from
      Localization.localRingHom_to_map p q (algebraMap R S) rfl r]
    exact IsScalarTower.algebraMap_apply R S C r
  let : IsNoetherianRing A :=
    IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  let : Module.Flat R C := inferInstance
  let : Module.Flat A C :=
    (Module.flat_iff_of_isLocalization A p.primeCompl C).mpr inferInstance
  let : Module A Nq := Module.restrictScalars A C Nq
  let : IsScalarTower A C Nq := IsScalarTower.restrictScalars A C Nq
  let : IsScalarTower R C Nq := IsScalarTower.to₁₃₄ R S C Nq
  let : IsScalarTower R A Nq := IsScalarTower.to₁₂₄ R A C Nq
  have hi : IsBaseChange A i := IsLocalizedModule.isBaseChange p.primeCompl A i
  have hj : IsBaseChange C j := IsLocalizedModule.isBaseChange q.primeCompl C j
  let u : M →ₗ[R] Nq := (j.restrictScalars R).comp f
  have hu : IsBaseChange C u := hf.comp hj
  let g : Mp →ₗ[A] Nq := hi.lift u
  have hg : IsBaseChange C g := by
    apply IsBaseChange.of_comp hi
    change IsBaseChange C ((g.restrictScalars R).comp i)
    rw [show (g.restrictScalars R).comp i = u from hi.lift_comp u]
    exact hu
  let : Module.Finite A Mp :=
    Module.Finite.of_isLocalizedModule (Rₚ := A) p.primeCompl i
  have hqLocal : IsAssociatedPrime (IsLocalRing.maximalIdeal C) Nq := by
    apply (open Module.associatedPrimes in
      mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule)
      q.primeCompl j
    change IsAssociatedPrime
      ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).under S) N
    rwa [Localization.AtPrime.under_maximalIdeal]
  have hpLocal : IsAssociatedPrime (IsLocalRing.maximalIdeal A) Mp :=
    IsAssociatedPrime.maximalIdeal_of_isBaseChange_of_flat_local
      (R := A) (S := C) g hg hqLocal
  have hback :=
    (open Module.associatedPrimes in
      comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg)
      p.primeCompl i (IsLocalRing.maximalIdeal A) hpLocal
      ((IsLocalRing.maximalIdeal A).comap (algebraMap R A)).fg_of_isNoetherianRing
  change IsAssociatedPrime
    ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).under R) M at hback
  rw [Localization.AtPrime.under_maximalIdeal] at hback
  exact hback


private theorem exists_prime_quotient_factor_of_associated_tensorProduct
    {R S : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∀ (q : Ideal S), IsAssociatedPrime q (S ⊗[R] M) →
      ∃ p : Ideal R, p.IsPrime ∧
        IsAssociatedPrime q (S ⧸ p.map (algebraMap R S)) := by
  induction ‹Module.Finite R M› using
    IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
    intro q hq
    exact (not_isAssociatedPrime_of_subsingleton hq).elim
  | quotient N p e =>
    intro q hq
    let e' : S ⊗[R] N ≃ₗ[S] S ⧸ p.asIdeal.map (algebraMap R S) :=
      (e.baseChange R S N (R ⧸ p.asIdeal)).trans
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S p.asIdeal).symm.toLinearEquiv
    exact ⟨p.asIdeal, p.isPrime, e'.isAssociatedPrime_iff.mp hq⟩
  | exact N₁ N₂ N₃ f g hf _ hfg ih₁ ih₃ =>
    intro q hq
    have hinj : Function.Injective (f.baseChange S) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap f hf
    have hexact : Function.Exact (f.baseChange S) (g.baseChange S) := by
      simpa only [LinearMap.baseChange_eq_ltensor] using Module.Flat.lTensor_exact S hfg
    have hmem := associatedPrimes.subset_union_of_exact
      (f := f.baseChange S) (g := g.baseChange S) hinj hexact hq
    rcases hmem with h₁ | h₃
    · exact ih₁ q h₁
    · exact ih₃ q h₃

/-- Under a flat algebra over a Noetherian ring, an associated prime of
the scalar extension of a finite module comes from its actual contracted
associated prime and is associated to the corresponding original
prime-quotient fiber. No Noetherianity of the target is required. -/
theorem IsAssociatedPrime.exists_quotient_of_flat_tensorProduct
    {R S M : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {q : Ideal S} (hq : IsAssociatedPrime q (S ⊗[R] M)) :
    ∃ p : Ideal R, IsAssociatedPrime p M ∧
      q.comap (algebraMap R S) = p ∧
      IsAssociatedPrime q (S ⧸ p.map (algebraMap R S)) := by
  obtain ⟨p, hp, hqp⟩ :=
    exists_prime_quotient_factor_of_associated_tensorProduct M q hq
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot S p
  have hqt : IsAssociatedPrime q (S ⊗[R] (R ⧸ p)) :=
    e.toLinearEquiv.isAssociatedPrime_iff.mp hqp
  have hcp : IsAssociatedPrime (q.comap (algebraMap R S)) (R ⧸ p) :=
    IsAssociatedPrime.comap_of_isBaseChange_of_flat
      (TensorProduct.mk R S (R ⧸ p) 1)
      (TensorProduct.isBaseChange (R := R) (M := R ⧸ p) (S := S)) hqt
  have hcontract : q.comap (algebraMap R S) = p :=
    (IsAssociatedPrime.eq_radical hp.isPrimary hcp).trans hp.radical
  have hbase : IsAssociatedPrime (q.comap (algebraMap R S)) M :=
    IsAssociatedPrime.comap_of_isBaseChange_of_flat (TensorProduct.mk R S M 1)
      (TensorProduct.isBaseChange (R := R) (M := M) (S := S)) hq
  exact ⟨p, hcontract ▸ hbase, hcontract, hqp⟩
