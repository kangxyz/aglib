/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.Covering
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# The chart locus of a point of the Grassmannian functor

For a point `N` of `G(k, A ⊗[R] M; A)` and a tuple `y : Fin k → M`, membership in the chart at
`1 ⊗ y` is Zariski local on `Spec A`, and the set of primes at which the chart map of `N` is
bijective is open: bijectivity at a prime `p` spreads to a basic open neighbourhood `D(r)`, and
then every base change inverting `r` lies in the chart. These are the ring-level inputs for the
statement that the charts are open subfunctors (Stacks, Tag 089T: "the inclusion `F_i ⊂ F` is
representable by open immersions").

## Main results

- `Module.Grassmannian.mem_chart_of_map_localization`: a point whose base changes to the
  `A_{s i}` lie in the chart at `y`, for `s` generating the unit ideal, lies in that chart.
- `Module.Grassmannian.exists_mem_chart_map_of_bijective`: if the chart map at `y` is bijective
  at a prime `p`, there is `r ∉ p` such that every base change inverting `r` lies in the chart.
-/

@[expose] public section

noncomputable section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
variable {A : Type w} [CommRing A] [Algebra R A]

/-- The chart condition is Zariski local on the base. -/
theorem mem_chart_of_map_localization [BaseChangeMkQFormula.{u, v, w} R M] {ι : Type*}
    (s : ι → A)
    (hs : Ideal.span (Set.range s) = ⊤) (y : Fin k → M) (N : G(k, A ⊗[R] M; A))
    (h : ∀ i, map (IsScalarTower.toAlgHom R A (Localization.Away (s i))) N ∈
      chart (Localization.Away (s i)) (baseChangeTuple (Localization.Away (s i)) y)) :
    N ∈ chart A (baseChangeTuple A y) := by
  rw [mem_chart_iff]
  apply bijective_of_localized_span (Set.range s) hs
  rintro ⟨_, i, rfl⟩
  exact (baseChange_localization_bijective_iff _ _).mp
    ((mem_chart_map_iff_of_algebraMap _ (fun _ ↦ rfl) y N).mp (h i))

/-- The chart locus is open: if the chart map of `N` at `y` is bijective at a prime `p`, then
there is `r ∉ p` such that the base change of `N` along every `R`-algebra map inverting `r` lies
in the chart at `1 ⊗ y`. -/
theorem exists_mem_chart_map_of_bijective [BaseChangeMkQFormula.{u, v, w} R M]
    (N : G(k, A ⊗[R] M; A)) (y : Fin k → M)
    (p : PrimeSpectrum A)
    (h : Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl
      (chartMap (baseChangeTuple A y) N.toSubmodule))) :
    ∃ r : A, r ∉ p.asIdeal ∧
      ∀ {B : Type w} [CommRing B] [Algebra R B] (f : A →ₐ[R] B), IsUnit (f r) →
        map f N ∈ chart B (baseChangeTuple B y) := by
  let S := p.asIdeal.primeCompl
  let Q := (A ⊗[R] M) ⧸ N.toSubmodule
  have : Module.FinitePresentation A Q := Module.finitePresentation_of_projective A Q
  have h' : Function.Bijective (IsLocalizedModule.map S
      (LocalizedModule.mkLinearMap S (Fin k → A)) (LocalizedModule.mkLinearMap S Q)
      (chartMap (baseChangeTuple A y) N.toSubmodule)) :=
    (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective _ _).mpr h
  obtain ⟨r, hr, hr'⟩ := exists_bijective_map_powers S
    (LocalizedModule.mkLinearMap S (Fin k → A)) (LocalizedModule.mkLinearMap S Q) _ h'
  refine ⟨r, hr, fun {B} _ _ f hu ↦ ?_⟩
  let ι : A →ₐ[R] Localization.Away r := IsScalarTower.toAlgHom R A (Localization.Away r)
  have h1 : map ι N ∈ chart (Localization.Away r) (baseChangeTuple (Localization.Away r) y) :=
    (mem_chart_map_iff_of_algebraMap ι (fun _ ↦ rfl) _ N).mpr
      ((baseChange_localization_bijective_iff _ _).mpr (hr' r dvd_rfl))
  have hunit : ∀ z : Submonoid.powers r, IsUnit (f z) := by
    rintro ⟨z, m, rfl⟩
    simpa using hu.pow m
  let ψ : Localization.Away r →ₐ[R] B := IsLocalization.liftAlgHom (M := Submonoid.powers r) hunit
  have hf : f = ψ.comp ι := by
    ext a
    simp [ψ, ι, IsLocalization.lift_eq]
  rw [hf, map_comp]
  exact map_mem_chart ψ _ h1

end Module.Grassmannian
