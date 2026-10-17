/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.Chart
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Local covering of the Grassmannian by coordinate charts

Let `N` be a point of `G(k, A ⊗[R] (Fin n → R); A)` with quotient `Q`, and let `p` be a prime
of `A`. The localization `Q_p` is a finitely presented flat module over the local ring `A_p`,
spanned by the classes of `1 ⊗ e_j`; a subfamily is a basis, and it has `k` elements because
the rank of `Q` at `p` is `k`. This gives a coordinate tuple `I : Fin k → Fin n` whose chart map
`A^k → Q` becomes bijective at `p`, hence on a basic open neighbourhood `D(r)` of `p`.

This is the covering step of Stacks, Tag 089T ("the collection `F_i`, `i ∈ I` covers `F`"),
where a basis of `Q_s ⊗ κ(s)` is extracted from the images of the standard basis.

## Main results

- `Module.Grassmannian.span_tmul_single_eq_top`: the vectors `1 ⊗ e_j` span `A ⊗[R] R^n`.
- `Module.Grassmannian.exists_localizedModule_bijective`: for every prime `p` there are a
  coordinate tuple `I` and `r ∉ p` such that the chart map at `1 ⊗ e_I` is bijective after
  localization away from `r`.
- `Module.Grassmannian.exists_mem_chart_map`: with `I` and `r` as above, the base change of the
  point along every `R`-algebra map inverting `r` lies in the coordinate chart at `I`.
-/

@[expose] public section

noncomputable section

universe u w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {k n : ℕ} {A : Type w} [CommRing A] [Algebra R A]

/-- The coordinate tuple `b ↦ e_{I b}` of `Fin n → R`. -/
abbrev coordinateTuple (R : Type u) [CommRing R] (I : Fin k → Fin n) : Fin k → Fin n → R :=
  fun b ↦ Pi.single (I b) 1

variable (R A) in
/-- The vectors `1 ⊗ e_j` span `A ⊗[R] (Fin n → R)`. -/
theorem span_tmul_single_eq_top :
    Submodule.span A
      (Set.range fun j : Fin n ↦ (1 : A) ⊗ₜ[R] (Pi.single j 1 : Fin n → R)) = ⊤ := by
  have h : (fun j : Fin n ↦ (1 : A) ⊗ₜ[R] (Pi.single j 1 : Fin n → R)) =
      ⇑(Algebra.TensorProduct.basis A (Pi.basisFun R (Fin n))) :=
    funext fun j ↦ by simp [Algebra.TensorProduct.basis_apply]
  rw [h]
  exact Basis.span_eq _

/-- For every prime `p` of `A` there are a coordinate tuple `I` and `r ∉ p` such that the chart
map `A^k → (A ⊗[R] R^n) ⧸ N` at `1 ⊗ e_I` becomes bijective after localization away from `r`
(Stacks, Tag 089T, covering step). -/
theorem exists_localizedModule_bijective (N : G(k, A ⊗[R] (Fin n → R); A))
    (p : PrimeSpectrum A) :
    ∃ (I : Fin k → Fin n) (r : A), r ∉ p.asIdeal ∧
      Function.Bijective (LocalizedModule.map (Submonoid.powers r)
        (chartMap (baseChangeTuple A (coordinateTuple R I)) N.toSubmodule)) := by
  classical
  let S := p.asIdeal.primeCompl
  let Q := (A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule
  have : Module.FinitePresentation A Q := Module.finitePresentation_of_projective A Q
  let Ap := Localization.AtPrime p.asIdeal
  let v : Fin n → LocalizedModule S Q := fun j ↦
    LocalizedModule.mkLinearMap S Q
      (N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] (Pi.single j 1 : Fin n → R)))
  have hv : Submodule.span Ap (Set.range v) = ⊤ := by
    have h1 : Submodule.span A (Set.range fun j : Fin n ↦
        N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] (Pi.single j 1 : Fin n → R))) = ⊤ := by
      rw [Set.range_comp' N.toSubmodule.mkQ, ← Submodule.map_span,
        span_tmul_single_eq_top R A, Submodule.map_top, Submodule.range_mkQ]
    have h2 := span_eq_top_of_isLocalizedModule Ap S (LocalizedModule.mkLinearMap S Q) h1
    rwa [← Set.range_comp] at h2
  have : Module.FinitePresentation Ap (LocalizedModule S Q) :=
    Module.finitePresentation_of_projective _ _
  obtain ⟨κ, a, b, hb⟩ := exists_basis_of_span_of_flat v hv
  have : Finite κ := Module.Finite.finite_basis b
  have hcard : Nat.card κ = k := by
    rw [← Module.finrank_eq_nat_card_basis b]
    exact N.rankAtStalk_eq p
  let e : Fin k ≃ κ := (Finite.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  let g := chartMap (baseChangeTuple A (coordinateTuple R (a ∘ e))) N.toSubmodule
  let bD := (Pi.basisFun A (Fin k)).ofIsLocalizedModule Ap S
    (LocalizedModule.mkLinearMap S (Fin k → A))
  have hmap : LocalizedModule.map S g = (bD.equiv b e).toLinearMap := by
    refine bD.ext fun c ↦ ?_
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, hb, Basis.ofIsLocalizedModule_apply,
      Pi.basisFun_apply, LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, chartMap_single]
    rfl
  have hbij : Function.Bijective (LocalizedModule.map S g) := by
    rw [hmap]
    exact (bD.equiv b e).bijective
  have hbij' : Function.Bijective (IsLocalizedModule.map S
      (LocalizedModule.mkLinearMap S (Fin k → A)) (LocalizedModule.mkLinearMap S Q) g) :=
    (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective _ _).mpr hbij
  obtain ⟨r, hr, hr'⟩ := exists_bijective_map_powers S
    (LocalizedModule.mkLinearMap S (Fin k → A)) (LocalizedModule.mkLinearMap S Q) g hbij'
  exact ⟨r, hr, hr' r dvd_rfl⟩

/-- Base change to a localization is bijective exactly when the localized map is. -/
theorem baseChange_localization_bijective_iff {P Q : Type*} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (S : Submonoid A) (g : P →ₗ[A] Q) :
    Function.Bijective (g.baseChange (Localization S)) ↔
      Function.Bijective (LocalizedModule.map S g) := by
  let hP := LocalizedModule.isBaseChange S P
  let hQ := LocalizedModule.isBaseChange S Q
  have key : hQ.equiv.toLinearMap ∘ₗ g.baseChange (Localization S) =
      LocalizedModule.map S g ∘ₗ hP.equiv.toLinearMap := by
    ext p
    simp [IsBaseChange.equiv_tmul]
  have hcomp : ⇑(g.baseChange (Localization S)) =
      hQ.equiv.symm ∘ LocalizedModule.map S g ∘ hP.equiv := by
    funext t
    apply hQ.equiv.injective
    simpa using LinearMap.congr_fun key t
  rw [hcomp, Function.Bijective.of_comp_iff' hQ.equiv.symm.bijective,
    Function.Bijective.of_comp_iff _ hP.equiv.bijective]

/-- The coordinate charts cover the Grassmannian locally: for every point `N` and prime `p`
there are a coordinate tuple `I` and `r ∉ p` such that the base change of `N` along every
`R`-algebra map inverting `r` lies in the chart at `1 ⊗ e_I` (Stacks, Tag 089T, covering
step). -/
theorem exists_mem_chart_map [BaseChangeMkQFormula.{u, u, w} R (Fin n → R)]
    (N : G(k, A ⊗[R] (Fin n → R); A)) (p : PrimeSpectrum A) :
    ∃ (I : Fin k → Fin n) (r : A), r ∉ p.asIdeal ∧
      ∀ {B : Type w} [CommRing B] [Algebra R B] (f : A →ₐ[R] B), IsUnit (f r) →
        map f N ∈ chart B (baseChangeTuple B (coordinateTuple R I)) := by
  obtain ⟨I, r, hr, hbij⟩ := exists_localizedModule_bijective N p
  refine ⟨I, r, hr, fun {B} _ _ f hu ↦ ?_⟩
  let ι : A →ₐ[R] Localization.Away r := IsScalarTower.toAlgHom R A (Localization.Away r)
  have h1 : map ι N ∈ chart (Localization.Away r)
      (baseChangeTuple (Localization.Away r) (coordinateTuple R I)) :=
    (mem_chart_map_iff_of_algebraMap ι (fun _ ↦ rfl) _ N).mpr
      ((baseChange_localization_bijective_iff _ _).mpr hbij)
  have hunit : ∀ y : Submonoid.powers r, IsUnit (f y) := by
    rintro ⟨y, m, rfl⟩
    simpa using hu.pow m
  let ψ : Localization.Away r →ₐ[R] B := IsLocalization.liftAlgHom (M := Submonoid.powers r) hunit
  have hf : f = ψ.comp ι := by
    ext a
    simp [ψ, ι, IsLocalization.lift_eq]
  rw [hf, map_comp]
  exact map_mem_chart ψ _ h1

end Module.Grassmannian
