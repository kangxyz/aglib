/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Aglib.AlgebraicGeometry.IdealSheaf.Restriction
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.Locus
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Singleton bases of actual closed-immersion stalk kernels

An actual closed-immersion kernel ideal module is locally rank one when its
actual stalk-map kernels have singleton bases and the ambient scheme is locally
Noetherian. No integrality or regularity condition is imposed on either scheme.

The canonical germ identifies the localized section kernel with the actual
stalk-map kernel. Finite presentation spreads its basis to a principal open.
Outside the closed image the localized ideal is the unit ideal. Canonical
spectral and restriction comparisons identify the resulting actual ideal modules.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open Module

namespace AlgebraicGeometry.Scheme.Hom

variable {C X : Scheme.{u}}

/-- On affine target opens, localization through the actual germ carries the
section kernel to the actual closed-immersion stalk-map kernel. -/
theorem ker_stalkMap_eq_map_ker_app (i : C ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (c : C) (hc : i c ∈ U) :
    RingHom.ker (i.stalkMap c).hom =
      (RingHom.ker (i.app U).hom).map (X.presheaf.germ U (i c) hc).hom := by
  have hV : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  have hcV : c ∈ i ⁻¹ᵁ U := by
    change i c ∈ U
    exact hc
  let A := Γ(X, U)
  let B := Γ(C, i ⁻¹ᵁ U)
  let S := X.presheaf.stalk (i c)
  let T := C.presheaf.stalk c
  let φ : A →+* B := (i.app U).hom
  let P := (hU.primeIdealOf ⟨i c, hc⟩).asIdeal
  let Q := (hV.primeIdealOf ⟨c, hcV⟩).asIdeal
  let : Algebra A S := X.presheaf.algebra_section_stalk ⟨i c, hc⟩
  let : Algebra B T := C.presheaf.algebra_section_stalk ⟨c, hcV⟩
  have : IsLocalization.AtPrime S P := hU.isLocalization_stalk ⟨i c, hc⟩
  have : IsLocalization.AtPrime T Q := hV.isLocalization_stalk ⟨c, hcV⟩
  have hpq : Q.comap φ = P := by
    simpa only [Hom.appLE_eq_app, PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE U hU (i ⁻¹ᵁ U) hV le_rfl hcV)
  have hcompl : (Q.comap φ).primeCompl = P.primeCompl := by
    ext a
    simp only [Ideal.mem_primeCompl_iff, hpq]
  have hmap : P.primeCompl.map φ = Q.primeCompl :=
    (congrArg (Submonoid.map φ) hcompl.symm).trans
      (Ideal.map_primeCompl_comap_of_surjective φ (i.app_surjective U hU) Q)
  let g : S →+* T := IsLocalization.map T φ (hmap.symm ▸ P.primeCompl.le_comap_map)
  have hg : g = (i.stalkMap c).hom := by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext a
    change g (algebraMap A S a) = (i.stalkMap c).hom (algebraMap A S a)
    calc
      g (algebraMap A S a) = algebraMap B T (φ a) :=
        IsLocalization.map_eq (hmap.symm ▸ P.primeCompl.le_comap_map) a
      _ = (i.stalkMap c).hom (algebraMap A S a) := by
        change (C.presheaf.germ (i ⁻¹ᵁ U) c hcV).hom ((i.app U).hom a) =
          (i.stalkMap c).hom ((X.presheaf.germ U (i c) hc).hom a)
        exact (i.germ_stalkMap_apply U c hc a).symm
  change RingHom.ker (i.stalkMap c).hom = (RingHom.ker φ).map (algebraMap A S)
  exact (congrArg (fun f : S →+* T ↦ RingHom.ker f) hg.symm).trans
    (IsLocalization.ker_map (S := S) T φ hmap)

/-- The section kernel has a singleton basis near every prime of every affine
target chart. The bases on the closed image come from actual stalk kernels. -/
private theorem affineKernel_localizedBasis_of_stalkKernelBasis
    [IsLocallyNoetherian X] (i : C ⟶ X) [IsClosedImmersion i]
    (hbasis : ∀ c : C, Nonempty (Basis PUnit.{u + 1} (X.presheaf.stalk (i c))
      (RingHom.ker (i.stalkMap c).hom)))
    (U : X.Opens) (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(X, U)) :
    ∃ s : Γ(X, U), s ∉ P.asIdeal ∧ Nonempty
      (Basis PUnit.{u + 1} (Localization.Away s)
        (LocalizedModule.Away s (RingHom.ker (i.app U).hom))) := by
  classical
  let A := Γ(X, U)
  let I := RingHom.ker (i.app U).hom
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Finite A I := Module.Finite.of_fg I.fg_of_isNoetherianRing
  have : Module.FinitePresentation A I := Module.finitePresentation_of_finite A I
  let x := hU.fromSpec P
  have hxU : x ∈ U := hU.range_fromSpec.subset ⟨P, rfl⟩
  by_cases hx : x ∈ Set.range i
  · obtain ⟨c, hc⟩ := hx
    have hcU : i c ∈ U := hc.symm ▸ hxU
    let S := X.presheaf.stalk (i c)
    let : Algebra A S := X.presheaf.algebra_section_stalk ⟨i c, hcU⟩
    let P' := hU.primeIdealOf ⟨i c, hcU⟩
    have : IsLocalization.AtPrime S P'.asIdeal := hU.isLocalization_stalk ⟨i c, hcU⟩
    have hP : P' = P := by
      apply hU.fromSpec.isOpenEmbedding.injective
      rw [hU.fromSpec_primeIdealOf]
      exact hc
    have hker : RingHom.ker (i.stalkMap c).hom = I.map (algebraMap A S) :=
      ker_stalkMap_eq_map_ker_app i U hU c hcU
    let b := (hbasis c).some
    let b' := b.map (LinearEquiv.ofEq _ _ hker)
    obtain ⟨s, hs, bs, -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
      P'.asIdeal.primeCompl (Algebra.idealMap S I) S b'
    exact ⟨s, by simpa only [Ideal.mem_primeCompl_iff, hP] using hs, ⟨bs⟩⟩
  · have hnot : ¬ I ≤ P.asIdeal := by
      intro hle
      have hsupport : x ∈ i.ker.support :=
        (i.ker.fromSpec_mem_support_iff ⟨U, hU⟩ P).mpr
          (by simpa only [Hom.ker_apply] using hle)
      change x ∈ (i.ker.support : Set X) at hsupport
      rw [Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq] at hsupport
      exact hx hsupport
    let S := Localization.AtPrime P.asIdeal
    have htop : I.map (algebraMap A S) = ⊤ := by
      obtain ⟨a, haI, haP⟩ := Set.not_subset.mp hnot
      exact (I.map (algebraMap A S)).eq_top_of_isUnit_mem
        (Ideal.mem_map_of_mem (algebraMap A S) haI)
        (IsLocalization.map_units S
          (⟨a, Ideal.mem_primeCompl_iff.mpr haP⟩ : P.asIdeal.primeCompl))
    have hb : Nonempty (Basis PUnit.{u + 1} S (I.map (algebraMap A S))) := by
      rw [htop]
      exact ⟨(Basis.singleton PUnit S).map
        (Submodule.topEquiv : (⊤ : Submodule S S) ≃ₗ[S] S).symm⟩
    obtain ⟨s, hs, bs, -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
      P.asIdeal.primeCompl (Algebra.idealMap S I) S hb.some
    exact ⟨s, Ideal.mem_primeCompl_iff.mp hs, ⟨bs⟩⟩

/-- Singleton bases of the actual stalk-map kernels give local rank one of
an actual closed-immersion ideal module over a locally Noetherian scheme.
The source scheme need not be integral. -/
theorem idealModule_isLocallyRankOne_of_stalkKernelBasis
    [IsLocallyNoetherian X] (i : C ⟶ X) [IsClosedImmersion i]
    (hbasis : ∀ c : C, Nonempty (Basis PUnit.{u + 1} (X.presheaf.stalk (i c))
      (RingHom.ker (i.stalkMap c).hom))) :
    IsLocallyRankOne X (idealModule i) := by
  apply isLocallyRankOne_of_forall_isLocallyRankOneAt
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let φ := i.app U
  have hspec : IsLocallyRankOne (Spec Γ(X, U)) (idealModule (Spec.map φ)) :=
    affineIdeal_rankOne_of_localizedBasis φ
      (affineKernel_localizedBasis_of_stalkKernelBasis i hbasis U hU)
  have : IsIso U.toSpecΓ := inferInstanceAs (IsIso hU.isoSpec.hom)
  have hV : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  have : IsIso (i ⁻¹ᵁ U).toSpecΓ := inferInstanceAs (IsIso hV.isoSpec.hom)
  have hsquare := Scheme.Opens.toSpecΓ_naturality i U
  have : IsIso (idealPullbackMap (Spec.map φ) (i ∣_ U) U.toSpecΓ
      (i ⁻¹ᵁ U).toSpecΓ hsquare) :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  have hlocal : IsLocallyRankOne U.toScheme (idealModule (i ∣_ U)) :=
    isLocallyRankOne_of_iso _
      (asIso (idealPullbackMap (Spec.map φ) (i ∣_ U) U.toSpecΓ
        (i ⁻¹ᵁ U).toSpecΓ hsquare)) (pullback_locallyRankOne U.toSpecΓ _ hspec)
  exact ⟨U.toScheme, U.ι, inferInstance, ⟨⟨x, hxU⟩, rfl⟩,
    isLocallyRankOne_of_iso _
      (asIso (idealPullbackMap i (i ∣_ U) U.ι (i ⁻¹ᵁ U).ι
        (morphismRestrict_ι i U).symm)).symm hlocal⟩

end AlgebraicGeometry.Scheme.Hom
