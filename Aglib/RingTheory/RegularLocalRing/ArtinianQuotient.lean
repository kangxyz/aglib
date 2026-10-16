/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.RegularPrincipal
public import Aglib.RingTheory.LocalRing.SeparatedPrincipal
public import Aglib.RingTheory.RegularLocalRing.Etale
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Artinian quotients of regular one-dimensional local rings

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native proof validation is pending the coordinated build.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open LinearMap
open Module
open IsLocalRing

section
namespace IsRegularLocalRing

/-- A one-dimensional regular local ring is a domain and a DVR. The domain
statement is derived, not assumed. -/
theorem regularLocal_dimension_one_dvr (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 1) :
    ∃ h : IsDomain R, @IsDiscreteValuationRing R _ h := by
  have hspan : (maximalIdeal R).spanFinrank = 1 := by
    have h := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hdim
    exact_mod_cast h
  obtain ⟨π, hπ⟩ := ((Submodule.spanFinrank_eq_one_iff _).mp hspan).1
  have hpowers : ∀ n : ℕ, π ^ n ≠ 0 := by
    intro n hn
    have hzero : Ring.KrullDimLE 0 R := .mk₀ fun P hP ↦ by
      have hπP : π ∈ P := hP.mem_of_pow_mem n (hn ▸ P.zero_mem)
      have hmP : maximalIdeal R ≤ P := by
        rw [hπ]
        exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπP)
      exact (maximalIdeal.isMaximal R).eq_of_le hP.ne_top hmP ▸ maximalIdeal.isMaximal R
    have hle := (Ring.krullDimLE_iff (R := R) (n := 0)).mp hzero
    rw [hdim] at hle
    norm_num at hle
  let hdomain := _root_.IsLocalRing.isDomain_of_isHausdorff_of_maximalIdeal_eq_span π hπ hpowers
  exact ⟨hdomain, _root_.IsLocalRing.isDiscreteValuationRing_of_isHausdorff_of_maximalIdeal_eq_span
    π hπ hpowers⟩

end IsRegularLocalRing
end

section
namespace RingHom

/-- A surjective map from a one-dimensional ring to a zero-dimensional ring has
nonzero kernel. The target may be the zero ring. -/
theorem ker_ne_bot_of_dimension_one_to_zero {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Ring.KrullDimLE 0 S]
    (f : R →+* S) (hsurj : Function.Surjective f) (hdim : ringKrullDim R = 1) :
    RingHom.ker f ≠ ⊥ := by
  intro hker
  let e := RingEquiv.ofBijective f ⟨(RingHom.injective_iff_ker_eq_bot f).mpr hker, hsurj⟩
  have hle : ringKrullDim S ≤ 0 := (Ring.krullDimLE_iff (R := S) (n := 0)).mp inferInstance
  rw [← ringKrullDim_eq_of_ringEquiv e, hdim] at hle
  norm_num at hle

end RingHom
end

section
namespace IsRegularLocalRing

/-- The actual kernel of an Artinian quotient of a one-dimensional regular
local ring has a singleton basis, with no reducedness hypothesis on the quotient. -/
def regularLocalArtinianKernelBasis {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsRegularLocalRing R] [IsArtinianRing S]
    (f : R →+* S) (hsurj : Function.Surjective f) (hdim : ringKrullDim R = 1) :
    Basis PUnit.{u + 1} R (RingHom.ker f) := by
  letI := (_root_.IsRegularLocalRing.regularLocal_dimension_one_dvr R hdim).choose
  letI := (_root_.IsRegularLocalRing.regularLocal_dimension_one_dvr R hdim).choose_spec
  exact _root_.Ideal.principalIdealBasis _ (_root_.RingHom.ker_ne_bot_of_dimension_one_to_zero f
    hsurj hdim)

end IsRegularLocalRing
end

section
namespace Ideal

/-- A regular one-dimensional local quotient ideal is locally free on a
principal neighborhood; an Artinian quotient is allowed to vanish. -/
theorem artinianQuotientIdeal_localizedBasis
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsArtinianRing S]
    (f : R →+* S) (hsurj : Function.Surjective f)
    (hlocal : ∀ (P : Ideal R) [P.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime P) ∧
        ringKrullDim (Localization.AtPrime P) = 1)
    (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧ Nonempty
      (Basis PUnit.{u + 1} (Localization.Away r)
        (LocalizedModule.Away r (RingHom.ker f))) := by
  obtain ⟨P, hP, hpP⟩ := p.asIdeal.exists_le_maximal p.2.ne_top
  let : P.IsMaximal := hP
  let : IsRegularLocalRing (Localization.AtPrime P) := (hlocal P).1
  let T := Localization (P.primeCompl.map f)
  let g : Localization.AtPrime P →+* T :=
    IsLocalization.map T f P.primeCompl.le_comap_map
  have hgsurj : Function.Surjective g :=
    IsLocalization.map_surjective_of_surjective P.primeCompl (Localization.AtPrime P) T hsurj
  let b := _root_.IsRegularLocalRing.regularLocalArtinianKernelBasis g hgsurj (hlocal P).2
  have hker : RingHom.ker g = (RingHom.ker f).map (algebraMap R (Localization.AtPrime P)) :=
    IsLocalization.ker_map T f rfl
  let b' := b.map (LinearEquiv.ofEq _ _ hker)
  have : Module.Finite R (RingHom.ker f) := Module.Finite.of_fg (Ideal.fg_of_isNoetherianRing _)
  have : Module.FinitePresentation R (RingHom.ker f) :=
    Module.finitePresentation_of_finite R (RingHom.ker f)
  obtain ⟨r, hr, br, -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    P.primeCompl (Algebra.idealMap (Localization.AtPrime P) (RingHom.ker f))
    (Localization.AtPrime P) b'
  exact ⟨r, fun h ↦ hr (hpP h), ⟨br⟩⟩

end Ideal
end

section
namespace RingHom

/-- In a ring with regular one-dimensional maximal localizations, the generator
of any principal kernel with Artinian quotient is a non-zero-divisor. -/
theorem artinianPrincipalKernel_isSMulRegular
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsArtinianRing S]
    (f : R →+* S) (hsurj : Function.Surjective f) (a : R)
    (hker : RingHom.ker f = Ideal.span {a})
    (hlocal : ∀ (P : Ideal R) [P.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime P) ∧
        ringKrullDim (Localization.AtPrime P) = 1) : IsSMulRegular R a := by
  intro x y hxy
  apply Module.eq_of_localization_maximal
    (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap R (Localization.AtPrime P)) x y
  intro P hP
  let : IsRegularLocalRing (Localization.AtPrime P) := (hlocal P).1
  let := (_root_.IsRegularLocalRing.regularLocal_dimension_one_dvr (Localization.AtPrime P) (hlocal
    P).2).choose
  let T := Localization (P.primeCompl.map f)
  let g : Localization.AtPrime P →+* T :=
    IsLocalization.map T f P.primeCompl.le_comap_map
  have hgsurj : Function.Surjective g :=
    IsLocalization.map_surjective_of_surjective P.primeCompl (Localization.AtPrime P) T hsurj
  have hkerloc : RingHom.ker g =
      Ideal.span {algebraMap R (Localization.AtPrime P) a} := by
    rw [IsLocalization.ker_map T f rfl, hker, Ideal.map_span, Set.image_singleton]
  have hane : algebraMap R (Localization.AtPrime P) a ≠ 0 := by
    intro ha
    apply _root_.RingHom.ker_ne_bot_of_dimension_one_to_zero g hgsurj (hlocal P).2
    rw [hkerloc, ha, Ideal.span_singleton_zero]
  apply mul_left_cancel₀ hane
  simpa only [Algebra.linearMap_apply, smul_eq_mul, map_mul] using
    congrArg (algebraMap R (Localization.AtPrime P)) hxy

end RingHom
end
