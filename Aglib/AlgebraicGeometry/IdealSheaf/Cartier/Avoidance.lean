/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Interfaces
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.IdealSheaf.Restriction
public import Aglib.RingTheory.Ideal.RegularPrincipal.BaseChange

/-!
# Cartier pullback along an integral scheme avoiding the divisor

The theorem concerns the original kernel/adjunction map on an actual pullback
square. Local regular generators stay nonzero on the integral source: otherwise
the closed inverse image of the divisor would contain a nonempty, hence dense,
open. The canonical affine comparison then proves that the original map is an
isomorphism. Neither flatness of the morphism nor Noetherianity is assumed.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X D Y D' : Scheme.{u}}

/-- The kernel ideal data in an actual cartesian square of a closed immersion is
the native inverse-image ideal data. -/
theorem ker_eq_comap_of_isPullback_of_isClosedImmersion
    (i : D ⟶ X) (i' : D' ⟶ Y) (f : Y ⟶ X) (a : D' ⟶ D)
    (H : IsPullback a i' i f) [IsClosedImmersion i] : i'.ker = i.ker.comap f := by
  have hsnd : (pullback.snd i f).ker = i.ker.comap f := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i f,
      ← Hom.ker_comp_of_isIso (pullbackSymmetry i f).hom (pullback.fst f i)]
    simp
  rw [← hsnd, ← Hom.ker_comp_of_isIso H.isoPullback.hom (pullback.snd i f)]
  simp

/-- An inverse-image ideal avoiding containment has a nonzero ideal on every
nonempty affine chart of an integral scheme. -/
theorem comap_ker_ideal_ne_bot_of_integral_avoidance
    [IsIntegral Y] (i : D ⟶ X) (f : Y ⟶ X) [IsClosedImmersion i]
    (havoid : ¬ Set.range f ⊆ Set.range i)
    (W : Y.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    (i.ker.comap f).ideal ⟨W, hW⟩ ≠ ⊥ := by
  intro hzero
  let J := i.ker.comap f
  have hsub : (W : Set Y) ⊆ J.support := by
    intro y hy
    have hp := (J.fromSpec_mem_support_iff ⟨W, hW⟩
      (hW.primeIdealOf ⟨y, hy⟩)).mpr (by rw [hzero]; exact bot_le)
    change hW.fromSpec (hW.primeIdealOf ⟨y, hy⟩) ∈ (J.support : Set Y) at hp
    rw [IsAffineOpen.fromSpec_primeIdealOf] at hp
    exact hp
  have hd : Dense (W : Set Y) := W.isOpen.dense
    ⟨(Classical.choice ‹Nonempty W›).val, (Classical.choice ‹Nonempty W›).property⟩
  have hall : (Set.univ : Set Y) ⊆ J.support := by
    rw [← hd.closure_eq]
    exact closure_minimal hsub J.support.isClosed
  apply havoid
  rintro _ ⟨y, rfl⟩
  have hy := hall (Set.mem_univ y)
  change y ∈ ((i.ker.comap f).support : Set Y) at hy
  simpa only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
    Set.mem_preimage, Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq] using hy

/-- The actual ideal pullback map on restricted affine charts is an isomorphism
when the actual section kernels have corresponding regular generators. -/
theorem idealPullbackMap_restricted_isIso_of_regularGenerator
    (i : D ⟶ X) (i' : D' ⟶ Y) (f : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ f) [IsClosedImmersion i] [IsClosedImmersion i']
    (U : X.Opens) (W : Y.Opens) (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (hWU : W ≤ f ⁻¹ᵁ U) (r : Γ(X, U)) (hr : IsSMulRegular Γ(X, U) r)
    (hgen : RingHom.ker (i.app U).hom = Ideal.span {r})
    (hr' : IsSMulRegular Γ(Y, W) (f.appLE U W hWU r))
    (hgen' : RingHom.ker (i'.app W).hom = Ideal.span {f.appLE U W hWU r}) :
    IsIso (idealPullbackMap (i ∣_ U) (i' ∣_ W) (f.resLE U W hWU)
      (restrictedSquareSourceMap i i' f a h U W hWU)
      (restrictedSquareSourceMap_comm i i' f a h U W hWU)) := by
  let hpre : i' ⁻¹ᵁ W ≤ a ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage]
    exact i'.preimage_mono hWU
  let φ := i.app U
  let φ' := i'.app W
  let b := f.appLE U W hWU
  let c := a.appLE (i ⁻¹ᵁ U) (i' ⁻¹ᵁ W) hpre
  have hDU : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  have hDW : IsAffineOpen (i' ⁻¹ᵁ W) := hW.preimage i'
  have : IsIso U.toSpecΓ := inferInstanceAs (IsIso hU.isoSpec.hom)
  have : IsIso W.toSpecΓ := inferInstanceAs (IsIso hW.isoSpec.hom)
  have : IsIso (i ⁻¹ᵁ U).toSpecΓ := inferInstanceAs (IsIso hDU.isoSpec.hom)
  have : IsIso (i' ⁻¹ᵁ W).toSpecΓ := inferInstanceAs (IsIso hDW.isoSpec.hom)
  have hs : Spec.map c ≫ Spec.map φ = Spec.map φ' ≫ Spec.map b := by
    apply (cancel_epi (i' ⁻¹ᵁ W).toSpecΓ).mp
    change (i' ⁻¹ᵁ W).toSpecΓ ≫ Spec.map c ≫ Spec.map φ =
      (i' ⁻¹ᵁ W).toSpecΓ ≫ Spec.map φ' ≫ Spec.map b
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE,
      Category.assoc, Scheme.Opens.toSpecΓ_naturality,
      ← Category.assoc (i' ⁻¹ᵁ W).toSpecΓ, Scheme.Opens.toSpecΓ_naturality,
      Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun q ↦ q ≫ U.toSpecΓ)
      (restrictedSquareSourceMap_comm i i' f a h U W hWU)
  have hc : φ ≫ c = b ≫ φ' := by
    apply Spec.map_injective
    simpa only [Spec.map_comp] using hs
  have : IsIso (ModuleCat.extendedKernelMap φ φ' b c hc) :=
    ModuleCat.extendedKernelMap_isIso_of_regularPrincipal φ φ' b c hc
      r hr hgen hr' hgen'
  have : IsIso (idealPullbackMap (Spec.map φ) (Spec.map φ')
      (Spec.map b) (Spec.map c) hs) :=
    affineIdealPullbackMap_isIso_of_scalarExtension φ φ' b c hc hs
  have hX := Scheme.Opens.toSpecΓ_naturality i U
  have hY := Scheme.Opens.toSpecΓ_naturality i' W
  have : IsIso (idealPullbackMap (Spec.map φ) (i ∣_ U)
      (asIso U.toSpecΓ).hom (asIso (i ⁻¹ᵁ U).toSpecΓ).hom hX) :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  have : IsIso (idealPullbackMap (Spec.map φ') (i' ∣_ W)
      (asIso W.toSpecΓ).hom (asIso (i' ⁻¹ᵁ W).toSpecΓ).hom hY) :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact idealPullbackMap_isIso_of_isoSquares (i ∣_ U) (i' ∣_ W) (f.resLE U W hWU)
    (restrictedSquareSourceMap i i' f a h U W hWU)
    (restrictedSquareSourceMap_comm i i' f a h U W hWU)
    (Spec.map φ) (Spec.map φ') (Spec.map b) (Spec.map c) hs
    (asIso U.toSpecΓ) (asIso (i ⁻¹ᵁ U).toSpecΓ)
    (asIso W.toSpecΓ) (asIso (i' ⁻¹ᵁ W).toSpecΓ) hX hY
    (Scheme.Opens.toSpecΓ_SpecMap_appLE f U W hWU)

/-- Pulling an actual Cartier ideal to an integral scheme whose image is not
contained in the divisor preserves the original canonical ideal map. -/
theorem idealPullbackMap_isIso_of_integral_avoidance
    [IsIntegral Y] (i : D ⟶ X) (i' : D' ⟶ Y) (f : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ f) (H : IsPullback a i' i f) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i))
    (havoid : ¬ Set.range f ⊆ Set.range i) :
    IsIso (idealPullbackMap i i' f a h) := by
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback H inferInstance
  have hker := ker_eq_comap_of_isPullback_of_isClosedImmersion i i' f a H
  apply idealPullbackMap_isIso_of_local i i' f a h
  intro y
  obtain ⟨U, hU, hyU, r, hr, hgen⟩ :=
    exists_affine_regular_idealGenerator_of_isLocallyRankOne i hI (f y)
  obtain ⟨W, hW, hyW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ f ⁻¹ᵁ U from hyU)
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  have hgen' : RingHom.ker (i'.app W).hom = Ideal.span {f.appLE U W hWU r} := by
    rw [← i'.ker_apply ⟨W, hW⟩, hker,
      Scheme.IdealSheafData.ideal_comap_eq_map_appLE i.ker f ⟨U, hU⟩ ⟨W, hW⟩ hWU,
      i.ker_apply ⟨U, hU⟩, hgen, Ideal.map_span, Set.image_singleton]
  have hrne : f.appLE U W hWU r ≠ 0 := by
    intro hz
    have hzero : (i.ker.comap f).ideal ⟨W, hW⟩ = ⊥ := by
      rw [← hker, i'.ker_apply ⟨W, hW⟩, hgen', hz, Ideal.span_singleton_zero]
    exact comap_ker_ideal_ne_bot_of_integral_avoidance i f havoid W hW hzero
  have hr' : IsSMulRegular Γ(Y, W) (f.appLE U W hWU r) := by
    intro v w hvw
    exact mul_left_cancel₀ hrne hvw
  exact ⟨U, W, hWU, hyW,
    idealPullbackMap_restricted_isIso_of_regularGenerator i i' f a h
      U W hU hW hWU r hr hgen hr' hgen'⟩

namespace Cartier

/-- The exact general avoidance family, inhabited on its original canonical map. -/
theorem integralAvoidanceCartierPullback : IntegralAvoidanceCartierPullback.{u} := by
  intro X D Y hY i f hi hI havoid
  let := hi
  exact idealPullbackMap_isIso_of_integral_avoidance i (pullback.snd i f) f
    (pullback.fst i f) (pullback.condition (f := i) (g := f))
    (IsPullback.of_hasPullback i f) hI havoid

end Cartier
end AlgebraicGeometry.Scheme.Hom
