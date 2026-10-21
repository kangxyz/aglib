/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.Cokernel
public import Aglib.RingTheory.Support.FiniteLengthDetection
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# Finite-length first Ext for modules projective off the closed point

A finite module over a Noetherian local ring, projective at every nonmaximal
prime, has finite-length first Ext into the ring. We clear denominators in
local splittings of a finite free presentation and use the original connecting
map. No general Ext-localization comparison is assumed or constructed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Abelian

namespace ModuleCat

private theorem exists_smul_retraction
    {R K P : Type u} [CommRing R] [AddCommGroup K] [Module R K]
    [AddCommGroup P] [Module R P] [Module.Finite R K] [Module.FinitePresentation R P]
    (S : Submonoid R) (i : K →ₗ[R] P)
    (ρ : LocalizedModule S P →ₗ[Localization S] LocalizedModule S K)
    (hρ : ρ.comp (LocalizedModule.map S i) = LinearMap.id) :
    ∃ (q : P →ₗ[R] K) (s : S), q.comp i = (s : R) • LinearMap.id := by
  let k := LocalizedModule.mkLinearMap S K
  let p := LocalizedModule.mkLinearMap S P
  obtain ⟨q, t, hq⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    S k ((ρ.restrictScalars R).comp p)
  have hcomp : k.comp (q.comp i) = k.comp ((t : R) • LinearMap.id) := by
    ext x
    have hqx := LinearMap.congr_fun hq (i x)
    change k (q (i x)) = (t : R) • ρ (p (i x)) at hqx
    have hρx : ρ (p (i x)) = k x := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply, k, p,
        LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk] using
        LinearMap.congr_fun hρ (k x)
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      map_smul] using hqx.trans (congrArg (fun y => (t : R) • y) hρx)
  obtain ⟨s, hs⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    S k (q.comp i) ((t : R) • LinearMap.id) hcomp
  refine ⟨(s : R) • q, s * t, ?_⟩
  simpa only [LinearMap.smul_comp, Submonoid.smul_def, smul_smul,
    Submonoid.coe_mul] using hs

private theorem exists_smul_retraction_of_projective_localization
    {R : Type u} [CommRing R] (S : Submonoid R)
    (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Module.Finite R T.X₁] [Module.FinitePresentation R T.X₂]
    [Module.Projective (Localization S) (LocalizedModule S T.X₃)] :
    ∃ (q : T.X₂ →ₗ[R] T.X₁) (s : S),
      q.comp T.f.hom = (s : R) • LinearMap.id := by
  let i := LocalizedModule.map S T.f.hom
  let g := LocalizedModule.map S T.g.hom
  have he : Function.Exact i g := IsLocalizedModule.map_exact S
    (LocalizedModule.mkLinearMap S T.X₁) (LocalizedModule.mkLinearMap S T.X₂)
    (LocalizedModule.mkLinearMap S T.X₃) T.f.hom T.g.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact)
  let U := ModuleCat.shortComplexOfCompEqZero i g (by
    ext x
    exact (he (i x)).mpr ⟨x, rfl⟩)
  have hU : U.ShortExact := ModuleCat.shortComplex_shortExact U he
    (LocalizedModule.map_injective S T.f.hom ((ModuleCat.mono_iff_injective T.f).mp hT.mono_f))
    (LocalizedModule.map_surjective S T.g.hom ((ModuleCat.epi_iff_surjective T.g).mp hT.epi_g))
  let σ := hU.splittingOfProjective
  apply exists_smul_retraction S T.f.hom σ.r.hom
  exact congrArg ModuleCat.Hom.hom σ.f_r

/-- A finite module projective at all nonmaximal primes of a Noetherian local
ring has finite-length first Ext into the ring. -/
theorem isFiniteLength_ext_one_of_projective_punctured
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Projective (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) :
    IsFiniteLength R (Ext M (ModuleCat.of R R) 1) := by
  apply Module.isFiniteLength_of_support_subset_closedPoint
  intro p hp
  by_contra hpm
  have hne : p.asIdeal ≠ IsLocalRing.maximalIdeal R := by
    intro heq
    apply hpm
    exact heq.symm.le
  have : Module.Projective (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) := hM p hne
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let T := f.shortComplexKer
  have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hf
  obtain ⟨q, s, hs⟩ := exists_smul_retraction_of_projective_localization
    p.asIdeal.primeCompl T hT
  have hkill (ξ : Ext M (ModuleCat.of R R) 1) : (s : R) • ξ = 0 := by
    obtain ⟨l, rfl⟩ := hT.homConnectingLinearMap_surjective (R := R) (ModuleCat.of R R) ξ
    rw [← map_smul]
    apply LinearMap.mem_ker.mp
    rw [hT.ker_homConnectingLinearMap (R := R) (ModuleCat.of R R)]
    refine ⟨ModuleCat.ofHom (l.hom.comp q), ?_⟩
    apply ModuleCat.hom_ext
    change (l.hom.comp q).comp T.f.hom = (s : R) • l.hom
    rw [LinearMap.comp_assoc, hs]
    ext x
    simp
  exact (Module.notMem_support_iff'.mpr fun ξ => ⟨(s : R), s.property, hkill ξ⟩) hp

/-- The punctured-free specialization of the projective-localization criterion. -/
theorem isFiniteLength_ext_one_of_free_punctured
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) :
    IsFiniteLength R (Ext M (ModuleCat.of R R) 1) := by
  apply isFiniteLength_ext_one_of_projective_punctured R M
  intro p hp
  let := hM p hp
  infer_instance

end ModuleCat
