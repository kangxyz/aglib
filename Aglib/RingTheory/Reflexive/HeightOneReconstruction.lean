/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.HeightOneLattice

/-! Surjectivity of an actual linear map from a reflexive module is detected in codimension one. -/

@[expose] public section

noncomputable section

namespace LinearMap

variable {R K M N Mₖ Nₖ : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Mₖ] [Module R Mₖ] [Module K Mₖ] [IsScalarTower R K Mₖ]
  [AddCommGroup Nₖ] [Module R Nₖ]
  [Module.FinitePresentation R M] [Module.FinitePresentation R (Module.Dual R M)]
  [Module.IsReflexive R M] [Module.IsTorsionFree R N]

include K

/-- If an actual map from a reflexive module to a torsion-free module is generically bijective
and its cokernel vanishes after clearing denominators outside every height-one prime, it is
surjective. All generic maps are the specified module-localization maps. -/
theorem surjective_of_generic_bijective_of_height_one
    (f : M →ₗ[R] N) (jM : M →ₗ[R] Mₖ) (jN : N →ₗ[R] Nₖ)
    [IsLocalizedModule (nonZeroDivisors R) jM] [IsLocalizedModule (nonZeroDivisors R) jN]
    (hgen : Function.Bijective (IsLocalizedModule.map (nonZeroDivisors R) jM jN f))
    (hloc : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      ∀ n : N, ∃ s ∉ p, s • n ∈ Set.range f) : Function.Surjective f := by
  have hjN : Function.Injective jN := by
    apply (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors R) jN).mpr
    intro s
    change IsSMulRegular N (s : R)
    exact (isRegular_iff_mem_nonZeroDivisors.mpr s.property).isSMulRegular
  intro n
  obtain ⟨x, hx⟩ := hgen.surjective (jN n)
  obtain ⟨m, hm⟩ := Module.IsReflexive.mem_range_of_forall_height_one
    (K := K) jM x (by
    intro p hp hh
    obtain ⟨s, hs, m, hm⟩ := hloc p hp hh n
    refine ⟨s, hs, m, hgen.injective ?_⟩
    rw [IsLocalizedModule.map_apply, map_smul, hx, hm, map_smul])
  refine ⟨m, hjN ?_⟩
  rw [← IsLocalizedModule.map_apply (nonZeroDivisors R) jM jN f, hm, hx]

/-- Generic bijectivity and surjectivity of the actual localized map at every height-one
prime imply surjectivity of a map from a reflexive module to a torsion-free module. -/
theorem surjective_of_generic_bijective_of_localized_height_one
    (f : M →ₗ[R] N) (jM : M →ₗ[R] Mₖ) (jN : N →ₗ[R] Nₖ)
    [IsLocalizedModule (nonZeroDivisors R) jM] [IsLocalizedModule (nonZeroDivisors R) jN]
    (hgen : Function.Bijective (IsLocalizedModule.map (nonZeroDivisors R) jM jN f))
    (hloc : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      Function.Surjective (LocalizedModule.map p.primeCompl f)) : Function.Surjective f := by
  apply surjective_of_generic_bijective_of_height_one (K := K) f jM jN hgen
  intro p hp hh n
  let := hp
  let := (localizedMap_surjective_iff_subsingleton_localized_coker p.primeCompl f).mp
    (hloc p hh)
  let q := LocalizedModule.mkLinearMap p.primeCompl (N ⧸ f.range)
  have hz : q (Submodule.Quotient.mk n) = 0 := Subsingleton.elim _ _
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl q).mp hz
  refine ⟨s, s.property, ?_⟩
  change Submodule.Quotient.mk ((s : R) • n) = 0 at hs
  exact (Submodule.Quotient.mk_eq_zero _).mp hs

end LinearMap
