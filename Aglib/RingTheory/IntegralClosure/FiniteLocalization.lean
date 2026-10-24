/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.Localization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# Finite normalization from the actual maximal localizations

A fixed normal principal open places the original normalization in one
principal localization. Its denominator filtration has finite terms;
one-step stabilization propagates. Finite quotient supports make these
stabilization loci open, and local normalization finiteness makes them
cover the prime spectrum. The actual normalization and coefficient maps
are retained throughout, without a normal-locus openness hypothesis.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace integralClosure

section Filtration

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The finite successive image in the quotient by the preceding term. -/
private def filtrationQuotient (F : ℕ →o Submodule R M) (n : ℕ) :
    Submodule R (M ⧸ F n) := (F (n + 1)).map (F n).mkQ

/-- The locus where a successive quotient vanishes after localization. -/
private def stabilizationLocus (F : ℕ →o Submodule R M) (n : ℕ) :
    Set (PrimeSpectrum R) := (Module.support R (filtrationQuotient F n))ᶜ

private theorem mem_stabilizationLocus_iff (F : ℕ →o Submodule R M)
    (n : ℕ) (p : PrimeSpectrum R) :
    p ∈ stabilizationLocus F n ↔
      ∀ x ∈ F (n + 1), ∃ r ∉ p.asIdeal, r • x ∈ F n := by
  constructor
  · intro hp x hx
    let q : filtrationQuotient F n := ⟨(F n).mkQ x, ⟨x, hx, rfl⟩⟩
    obtain ⟨r, hr, heq⟩ := (Module.notMem_support_iff'.mp hp) q
    refine ⟨r, hr, ?_⟩
    have hval := congrArg Subtype.val heq
    change r • (F n).mkQ x = 0 at hval
    rw [← map_smul] at hval
    exact (Submodule.Quotient.mk_eq_zero (F n)).mp hval
  · intro h
    apply Module.notMem_support_iff'.mpr
    intro q
    obtain ⟨x, hx, hqx⟩ := q.property
    obtain ⟨r, hr, hrx⟩ := h x hx
    refine ⟨r, hr, ?_⟩
    apply Subtype.ext
    change r • q.val = 0
    rw [← hqx, ← map_smul]
    exact (Submodule.Quotient.mk_eq_zero (F n)).mpr hrx

private theorem stabilizationLocus_mono (F : ℕ →o Submodule R M) (f : R)
    (hstep : ∀ n x, x ∈ F (n + 1) ↔ f • x ∈ F n) :
    Monotone (stabilizationLocus F) := by
  apply monotone_nat_of_le_succ
  intro n p hp
  apply (mem_stabilizationLocus_iff F (n + 1) p).mpr
  intro x hx
  obtain ⟨r, hr, hrx⟩ := (mem_stabilizationLocus_iff F n p).mp hp
    (f • x) ((hstep (n + 1) x).mp hx)
  refine ⟨r, hr, (hstep n (r • x)).mpr ?_⟩
  rwa [smul_comm] at hrx

private theorem exists_stabilization_atPrime
    (F : ℕ →o Submodule R M) (hfull : ∀ x, ∃ n, x ∈ F n)
    (p : Ideal R) [p.IsPrime]
    [Module.Finite (Localization.AtPrime p) (LocalizedModule p.primeCompl M)] :
    ∃ n, (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ stabilizationLocus F n := by
  let Rₚ := Localization.AtPrime p
  let Mₚ := LocalizedModule p.primeCompl M
  let l : M →ₗ[R] Mₚ := LocalizedModule.mkLinearMap p.primeCompl M
  let G : ℕ →o Submodule Rₚ Mₚ := {
    toFun := fun n ↦ (F n).localized' Rₚ p.primeCompl l
    monotone' := by
      intro i j hij x hx
      obtain ⟨y, hy, s, hys⟩ := hx
      exact ⟨y, F.monotone hij hy, s, hys⟩ }
  have hFsup : (⨆ n, F n) = ⊤ := by
    apply eq_top_iff.mpr
    intro x hx
    obtain ⟨n, hn⟩ := hfull x
    exact (le_iSup F n) hn
  have hGsup : (⨆ n, G n) = ⊤ := by
    change (⨆ n, (F n).localized' Rₚ p.primeCompl l) = ⊤
    rw [← Submodule.localized'_iSup, hFsup, Submodule.localized'_top]
  obtain ⟨n, hn⟩ := (Module.finite_def.mp
    (inferInstance : Module.Finite Rₚ Mₚ)).stabilizes_of_iSup_eq G hGsup
  refine ⟨n, (mem_stabilizationLocus_iff F n _).mpr ?_⟩
  intro x hx
  have hmem : l x ∈ G n := by rw [← hn]; trivial
  obtain ⟨y, hy, s, hys⟩ := hmem
  have heq : l y = l ((s : R) • x) := by
    rw [map_smul]
    exact IsLocalizedModule.mk'_eq_iff.mp hys
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq
    (S := p.primeCompl) (f := l) heq
  refine ⟨(t : R) * (s : R), p.primeCompl.mul_mem t.property s.property, ?_⟩
  have hy' := (F n).smul_mem (t : R) hy
  change (t : R) • y = (t : R) • ((s : R) • x) at ht
  rw [← mul_smul] at ht
  exact ht ▸ hy'

private theorem eq_top_of_one_step_stabilization
    (F : ℕ →o Submodule R M) (f : R)
    (hstep : ∀ n x, x ∈ F (n + 1) ↔ f • x ∈ F n)
    (hfull : ∀ x, ∃ n, x ∈ F n) (n : ℕ) (heq : F n = F (n + 1)) :
    F n = ⊤ := by
  have htail : ∀ k, F (n + k) = F n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      apply le_antisymm
      · intro x hx
        have hfx : f • x ∈ F (n + k) :=
          (hstep (n + k) x).mp (by simpa only [Nat.add_succ] using hx)
        have hfx' : f • x ∈ F n := ih ▸ hfx
        exact heq.symm ▸ (hstep n x).mpr hfx'
      · exact F.monotone (by omega)
  apply eq_top_iff.mpr
  intro x hx
  obtain ⟨k, hk⟩ := hfull x
  have hk' : x ∈ F (n + k) := F.monotone (by omega) hk
  exact htail k ▸ hk'

private theorem finite_of_denominatorFiltration
    (F : ℕ →o Submodule R M) (f : R)
    (hfg : ∀ n, (F n).FG)
    (hstep : ∀ n x, x ∈ F (n + 1) ↔ f • x ∈ F n)
    (hfull : ∀ x, ∃ n, x ∈ F n)
    (hlocal : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Finite (Localization.AtPrime m) (LocalizedModule m.primeCompl M)) :
    Module.Finite R M := by
  classical
  let : ∀ n, Module.Finite R (filtrationQuotient F n) :=
    fun n ↦ Module.Finite.of_fg ((hfg (n + 1)).map (F n).mkQ)
  have hUopen (n : ℕ) : IsOpen (stabilizationLocus F n) :=
    (Module.isClosed_support (R := R) (M := filtrationQuotient F n)).isOpen_compl
  have hUmono := stabilizationLocus_mono F f hstep
  have hcover : Set.univ ⊆ ⋃ n, stabilizationLocus F n := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
    let : m.IsMaximal := hm
    let : Module.Finite (Localization.AtPrime m) (LocalizedModule m.primeCompl M) := hlocal m
    obtain ⟨n, hn⟩ := exists_stabilization_atPrime F hfull m
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    intro hp'
    exact hn (Module.mem_support_mono hpm hp')
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (stabilizationLocus F) hUopen hcover
  let n := t.sup (fun i : ℕ ↦ i)
  have hUall (p : PrimeSpectrum R) : p ∈ stabilizationLocus F n := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ p))
    obtain ⟨hit, hpi⟩ := Set.mem_iUnion.mp hi
    exact hUmono (Finset.le_sup hit) hpi
  have hempty : Module.support R (filtrationQuotient F n) = ∅ := by
    ext p
    simp only [Set.mem_empty_iff_false, iff_false]
    exact hUall p
  let : Subsingleton (filtrationQuotient F n) := Module.support_eq_empty_iff.mp hempty
  have heq : F n = F (n + 1) := by
    apply le_antisymm (F.monotone (Nat.le_succ n))
    intro x hx
    have hzero : (F n).mkQ x = 0 := congrArg Subtype.val
      (Subsingleton.elim (⟨(F n).mkQ x, ⟨x, hx, rfl⟩⟩ : filtrationQuotient F n) 0)
    exact (Submodule.Quotient.mk_eq_zero (F n)).mp hzero
  have htop := eq_top_of_one_step_stabilization F f hstep hfull n heq
  exact Module.finite_def.mpr (htop ▸ hfg n)

/-- Powers of one fixed scalar pull back a finite denominator-zero module. -/
private def powerFiltration (T : Submodule R M) (f : R) : ℕ →o Submodule R M where
  toFun n := T.comap (LinearMap.lsmul R M (f ^ n))
  monotone' := by
    apply monotone_nat_of_le_succ
    intro n x hx
    change f ^ (n + 1) • x ∈ T
    rw [pow_succ', mul_smul]
    exact T.smul_mem f hx

private theorem mem_powerFiltration_succ (T : Submodule R M) (f : R) (n : ℕ) (x : M) :
    x ∈ powerFiltration T f (n + 1) ↔ f • x ∈ powerFiltration T f n := by
  change f ^ (n + 1) • x ∈ T ↔ f ^ n • (f • x) ∈ T
  rw [pow_succ, mul_smul]

end Filtration

section Normalization

universe u v

variable (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private theorem normalization_powerFiltration_fg (f : R) (hf : f ≠ 0) (n : ℕ) :
    (powerFiltration (LinearMap.range (Algebra.linearMap R (integralClosure R K))) f n).FG := by
  let N := integralClosure R K
  let T : Submodule R N := LinearMap.range (Algebra.linearMap R N)
  let F := powerFiltration T f
  let g : F n →ₗ[R] T := LinearMap.codRestrict T
    ((LinearMap.lsmul R N (f ^ n)).comp (F n).subtype) (fun x ↦ x.property)
  have hreg : IsSMulRegular N (f ^ n) := by
    intro x y h
    apply Subtype.ext
    have hK : f ^ n • (x : K) = f ^ n • (y : K) :=
      ((integralClosure R K).val.toLinearMap.map_smul (f ^ n) x).symm.trans
        ((congrArg (integralClosure R K).val h).trans
          ((integralClosure R K).val.toLinearMap.map_smul (f ^ n) y))
    simp only [Algebra.smul_def] at hK
    exact mul_left_cancel₀
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hf))) hK
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact hreg (congrArg Subtype.val h)
  exact Module.Finite.iff_fg.mp (Module.Finite.of_injective g hg)

omit [IsNoetherianRing R] in
private theorem normalization_powerFiltration_exhaustive
    (f : R) (hf : f ≠ 0) [IsIntegrallyClosed (Localization.Away f)]
    (x : integralClosure R K) :
    ∃ n, x ∈ powerFiltration
      (LinearMap.range (Algebra.linearMap R (integralClosure R K))) f n := by
  let A := Localization.Away f
  have hM : Submonoid.powers f ≤ nonZeroDivisors R := by
    rintro a ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hf)
  let : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A hM
  let φ : A →ₐ[R] K := IsLocalization.liftAlgHom
    (M := Submonoid.powers f) (f := Algebra.ofId R K)
    (fun s ↦ IsLocalization.map_units K ⟨s.val, hM s.property⟩)
  let : Algebra A K := φ.toRingHom.toAlgebra
  let : IsScalarTower R A K := IsScalarTower.of_algHom φ
  let : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) A K
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (show IsIntegral A (x : K) from x.property.tower_top)
  obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) y
  obtain ⟨n, hn⟩ := s.property
  refine ⟨n, r, ?_⟩
  apply Subtype.ext
  have hK := congrArg (algebraMap A K) hs
  rw [map_mul, ← IsScalarTower.algebraMap_apply R A K,
    ← IsScalarTower.algebraMap_apply R A K, hy, ← hn] at hK
  calc
    ((Algebra.linearMap R (integralClosure R K)) r : K) = algebraMap R K r :=
      (integralClosure R K).val.commutes r
    _ = algebraMap R K (f ^ n) * (x : K) := hK.symm.trans (mul_comm _ _)
    _ = (((LinearMap.lsmul R (integralClosure R K)) (f ^ n)) x : K) :=
      (((integralClosure R K).val.toLinearMap.map_smul (f ^ n) x).trans
        (Algebra.smul_def (f ^ n) (x : K))).symm

/-- The actual map from a prime localization into the supplied original
fraction field, extending its original coefficient map. -/
def atPrimeFractionMap (p : Ideal R) [p.IsPrime] : Localization.AtPrime p →ₐ[R] K :=
  IsLocalization.liftAlgHom (M := p.primeCompl) (f := Algebra.ofId R K)
    (fun s ↦ IsLocalization.map_units K ⟨s.val, p.primeCompl_le_nonZeroDivisors s.property⟩)

/-- A fixed nonzero normal principal open and finiteness of every literal
maximal-local normalization imply finiteness of the original normalization.
Every local coefficient action is the actual localization lift into the
supplied original fraction field. -/
theorem finite_of_normal_away_of_finite_atMaximal
    (f : R) (hf : f ≠ 0) [IsIntegrallyClosed (Localization.Away f)]
    (hlocal : ∀ (m : Ideal R) [m.IsMaximal],
      let _ : Algebra (Localization.AtPrime m) K := (atPrimeFractionMap R K m).toRingHom.toAlgebra
      Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) K)) :
    Module.Finite R (integralClosure R K) := by
  let N := integralClosure R K
  let T : Submodule R N := LinearMap.range (Algebra.linearMap R N)
  let F := powerFiltration T f
  apply finite_of_denominatorFiltration F f
    (normalization_powerFiltration_fg R K f hf) (mem_powerFiltration_succ T f)
    (normalization_powerFiltration_exhaustive R K f hf)
  intro m hm
  let Rₘ := Localization.AtPrime m
  let φ : Rₘ →ₐ[R] K := atPrimeFractionMap R K m
  let : Algebra Rₘ K := φ.toRingHom.toAlgebra
  let : IsScalarTower R Rₘ K := IsScalarTower.of_algHom φ
  let : Module.Finite Rₘ (integralClosure Rₘ K) := hlocal m
  let l : N →ₗ[R] integralClosure Rₘ K := (scalarExtensionHom R Rₘ K).toLinearMap
  let : IsLocalizedModule m.primeCompl l := scalarExtensionHom_isLocalizedModule R Rₘ K m.primeCompl
  let e : LocalizedModule m.primeCompl N ≃ₗ[Rₘ] integralClosure Rₘ K :=
    (IsLocalizedModule.iso m.primeCompl l).extendScalarsOfIsLocalization m.primeCompl Rₘ
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

end Normalization

end integralClosure
