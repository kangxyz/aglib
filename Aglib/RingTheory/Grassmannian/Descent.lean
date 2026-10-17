/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.BaseChange
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Zariski separatedness of the Grassmannian functor

A point of `G(k, A ⊗[R] M; A)` is determined by its base changes to the localizations
`A_{s i}` for a family `s` generating the unit ideal. This is the uniqueness half of the
Zariski sheaf property of the Grassmannian functor used in Stacks, Tag 089T ("`F` satisfies the
sheaf property for the Zariski topology").

## Main results

- `Module.Grassmannian.baseChangeMkQ_rTensor`: `baseChangeMkQ` sends the image of `v` to
  `1 ⊗ [v]`.
- `Module.Grassmannian.map_toSubmodule_of_algebraMap`: the submodule of `map f N` for an
  arbitrary algebra structure with algebra map `f`.
- `Module.Grassmannian.eq_of_map_localization_eq`: two points with equal base changes to all
  `A_{s i}` are equal.
- `Module.Grassmannian.rTensor_mem_map_iff_of_isLocalization`: for a localization `B` of `A`
  away from `r`, the image of `v` lies in the base change of `N` to `B` if and only if
  `r ^ m • v ∈ N` for some `m`.
- `Module.Grassmannian.finite_projective_rankAtStalk_of_localizationSpan`: being finite
  projective of constant rank `k` is local for a family generating the unit ideal. This is the
  condition on the quotient in the gluing half of the sheaf property.
-/

@[expose] public section

noncomputable section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
variable {A : Type w} [CommRing A] [Algebra R A] {B : Type w} [CommRing B] [Algebra R B]

/-- `baseChangeMkQ` sends the image of `v ∈ A ⊗[R] M` in `B ⊗[R] M` to `1 ⊗ [v]`. -/
theorem baseChangeMkQ_rTensor [BaseChangeMkQFormula.{u, v, w} R M] [Algebra A B]
    [IsScalarTower R A B]
    (N : Submodule A (A ⊗[R] M)) (v : A ⊗[R] M) :
    baseChangeMkQ B N
        (LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap v) =
      (1 : B) ⊗ₜ[A] N.mkQ v := by
  induction v using TensorProduct.inductionOn with
  | tmul a m =>
    have h : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
      baseChangeMkQ_tmul, h, map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one]
  | add v w hv hw => simp [hv, hw, TensorProduct.tmul_add]

/-- The submodule of `map f N` for an algebra structure on `B` over `A` with algebra map `f`. -/
theorem map_toSubmodule_of_algebraMap (f : A →ₐ[R] B) [inst : Algebra A B]
    [IsScalarTower R A B] (hf : ∀ a, algebraMap A B a = f a) (N : G(k, A ⊗[R] M; A)) :
    (map f N).toSubmodule = LinearMap.ker (baseChangeMkQ B N.toSubmodule) := by
  obtain rfl : inst = f.toAlgebra := Algebra.algebra_ext _ _ hf
  exact map_toSubmodule f N

/-- A point of the Grassmannian is determined by its base changes to the localizations at a
family generating the unit ideal (Zariski separatedness of the Grassmannian functor). -/
theorem eq_of_map_localization_eq [BaseChangeMkQFormula.{u, v, w} R M] {ι : Type*}
    (s : ι → A)
    (hs : Ideal.span (Set.range s) = ⊤) {N N' : G(k, A ⊗[R] M; A)}
    (h : ∀ i, map (IsScalarTower.toAlgHom R A (Localization.Away (s i))) N =
      map (IsScalarTower.toAlgHom R A (Localization.Away (s i))) N') :
    N = N' := by
  suffices H : ∀ {N N' : G(k, A ⊗[R] M; A)},
      (∀ i, map (IsScalarTower.toAlgHom R A (Localization.Away (s i))) N =
        map (IsScalarTower.toAlgHom R A (Localization.Away (s i))) N') →
      N.toSubmodule ≤ N'.toSubmodule from
    ext (le_antisymm (H h) (H fun i ↦ (h i).symm))
  intro N N' h v hv
  have key : ∀ i, ∃ m : ℕ, s i ^ m • N'.toSubmodule.mkQ v = 0 := by
    intro i
    let f := IsScalarTower.toAlgHom R A (Localization.Away (s i))
    have hf : ∀ a, algebraMap A (Localization.Away (s i)) a = f a := fun _ ↦ rfl
    have h1 : LinearMap.rTensor M f.toLinearMap v ∈ (map f N).toSubmodule := by
      rw [map_toSubmodule_of_algebraMap f hf, LinearMap.mem_ker, baseChangeMkQ_rTensor,
        Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hv, TensorProduct.tmul_zero]
    rw [h i, map_toSubmodule_of_algebraMap f hf, LinearMap.mem_ker, baseChangeMkQ_rTensor] at h1
    have h2 := congrArg (LocalizedModule.isBaseChange (Submonoid.powers (s i))
      ((A ⊗[R] M) ⧸ N'.toSubmodule)).equiv h1
    rw [IsBaseChange.equiv_tmul, one_smul, map_zero, LocalizedModule.mkLinearMap_apply,
      ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h2
    obtain ⟨⟨_, m, rfl⟩, hu⟩ := h2
    refine ⟨m, ?_⟩
    simpa [Submonoid.smul_def] using hu
  have : N'.toSubmodule.mkQ v ∈ (⊥ : Submodule A ((A ⊗[R] M) ⧸ N'.toSubmodule)) :=
    Submodule.mem_of_span_eq_top_of_smul_pow_mem ⊥ (Set.range s) hs _ fun ⟨_, i, hi⟩ ↦ by
      obtain ⟨m, hm⟩ := key i
      exact ⟨m, by simpa [← hi] using hm⟩
  simpa using this

/-- Let `B` be a localization of `A` away from `r`. The image of `v` lies in the base change of
`N` to `B` if and only if some power of `r` multiplies `v` into `N`. -/
theorem rTensor_mem_map_iff_of_isLocalization [BaseChangeMkQFormula.{u, v, w} R M] (r : A)
    [Algebra A B] [IsScalarTower R A B]
    [IsLocalization.Away r B] (N : G(k, A ⊗[R] M; A)) (v : A ⊗[R] M) :
    LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap v ∈
        (map (IsScalarTower.toAlgHom R A B) N).toSubmodule ↔
      ∃ m : ℕ, r ^ m • v ∈ N.toSubmodule := by
  let f := IsScalarTower.toAlgHom R A B
  have hf : ∀ a, algebraMap A B a = f a := fun _ ↦ rfl
  let Q := (A ⊗[R] M) ⧸ N.toSubmodule
  have hloc : IsLocalizedModule (Submonoid.powers r) (TensorProduct.mk A B Q 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) B _).mpr
      (TensorProduct.isBaseChange A Q B)
  rw [map_toSubmodule_of_algebraMap f hf, LinearMap.mem_ker, baseChangeMkQ_rTensor]
  constructor
  · intro h1
    obtain ⟨⟨_, m, rfl⟩, hc⟩ :=
      (IsLocalizedModule.eq_zero_iff (Submonoid.powers r) (TensorProduct.mk A B Q 1)).mp h1
    refine ⟨m, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa [Submonoid.smul_def] using hc
  · rintro ⟨m, hm⟩
    have hu : IsUnit (algebraMap A B (r ^ m)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit r).pow m
    have h0 : (r ^ m) • ((1 : B) ⊗ₜ[A] N.toSubmodule.mkQ v) = 0 := by
      rw [← TensorProduct.tmul_smul, ← map_smul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero _).mpr hm, TensorProduct.tmul_zero]
    rw [← algebraMap_smul B] at h0
    exact hu.smul_eq_zero.mp h0

/-- Being finite projective of constant rank `k` is a Zariski-local property of modules: it can
be checked on the localizations at a family generating the unit ideal. -/
theorem finite_projective_rankAtStalk_of_localizationSpan {Q : Type*} [AddCommGroup Q]
    [Module A Q] (s : Set A) (hs : Ideal.span s = ⊤)
    (hfin : ∀ g : s, Module.Finite (Localization.Away g.1) (LocalizedModule.Away g.1 Q))
    (hproj : ∀ g : s, Module.Projective (Localization.Away g.1) (LocalizedModule.Away g.1 Q))
    (hrank : ∀ g : s, ∀ p,
      rankAtStalk (R := Localization.Away g.1) (LocalizedModule.Away g.1 Q) p = k) :
    Module.Finite A Q ∧ Module.Projective A Q ∧ ∀ p, rankAtStalk (R := A) Q p = k := by
  have hfp : Module.FinitePresentation A Q :=
    Module.FinitePresentation.of_localizationSpan s hs fun g ↦
      have := hfin g
      have := hproj g
      Module.finitePresentation_of_projective _ _
  have hcover : ∀ p : PrimeSpectrum A, ∃ g : s, p ∈ PrimeSpectrum.basicOpen g.1 := by
    intro p
    by_contra! H
    have hle : Ideal.span s ≤ p.asIdeal := by
      rw [Ideal.span_le]
      intro g hg
      simpa [PrimeSpectrum.mem_basicOpen] using H ⟨g, hg⟩
    exact p.isPrime.ne_top (top_le_iff.mp (hs ▸ hle))
  have hproj' : Module.Projective A Q := by
    rw [← Module.freeLocus_eq_univ_iff]
    refine Set.eq_univ_of_forall fun p ↦ ?_
    obtain ⟨g, hg⟩ := hcover p
    have := hproj g
    exact (Module.basicOpen_subset_freeLocus_iff.mpr this) hg
  refine ⟨inferInstance, hproj', fun p ↦ ?_⟩
  · obtain ⟨g, hg⟩ := hcover p
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away g.1))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g.1) g.1]
      exact hg
    obtain ⟨p', rfl⟩ := hp
    rw [← Module.rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers g.1) Q)]
    exact hrank g p'

end Module.Grassmannian
