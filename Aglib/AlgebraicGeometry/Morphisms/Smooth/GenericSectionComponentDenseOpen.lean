/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.GenericSectionComponentIntegrality
public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothGenericIntegrality
public import Aglib.AlgebraicGeometry.Limits.ImmersionBaseChange

/-! # A genuine section component over a dense principal base open

The original descended clopen is restricted at one later principal stage.
Its original generic preimage and section are preserved, and all its fibres
are geometrically integral. The argument retains the original base and
fraction field. Relative component-locus openness over the entire base is
not asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

universe u

/-- The original stage transition square also lies over the original base. -/
private theorem stageTransition_isPullback_original
    {R : Type u} [CommRing R] (M : Submonoid R)
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
    {s t : Finset M} (h : op t ⟶ op s) :
    IsPullback ((baseChangeDiagram M p).map h)
      (pullback.fst (Spec.algebraMap R (stage M t)) p)
      (pullback.fst (Spec.algebraMap R (stage M s)) p ≫
        Spec.algebraMap R (stage M s)) (Spec.algebraMap R (stage M t)) := by
  have H : IsPullback ((baseChangeDiagram M p).map h)
      (pullback.fst (Spec.algebraMap R (stage M t)) p)
      (pullback.fst (Spec.algebraMap R (stage M s)) p)
      ((specDiagram M).map h) :=
    (isPullback_overPullbackMap p ((baseDiagram M).map h)).flip
  have he : (specDiagram M).map h ≫ Spec.algebraMap R (stage M s) =
      Spec.algebraMap R (stage M t) :=
    ((baseStructure M).naturality h).trans (Category.comp_id _)
  have H' := Pullback.Transport.exceptional_intersection_postcompose H
    (Spec.algebraMap R (stage M s))
  simpa only [he] using H'

/-- The full native double-base-change comparison transports geometric
integrality along an original factorization of base maps. -/
private theorem geometricallyIntegral_baseChange_of_factorization
    {X S T U : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S) (c : U ⟶ T) (g : U ⟶ S)
    (hg : c ≫ b = g) [GeometricallyIntegral (pullback.snd f b)] :
    GeometricallyIntegral (pullback.snd f g) := by
  let e := pullbackLeftPullbackSndIso f b c ≪≫ pullback.congrHom rfl hg
  have he : e.hom ≫ pullback.snd f g = pullback.snd (pullback.snd f b) c := by
    simp [e, pullback.map]
  have hh : GeometricallyIntegral (e.hom ≫ pullback.snd f g) := by
    rw [he]
    infer_instance
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)
    e.hom (pullback.snd f g)).mp hh

/-- Construct the original localization factor, its spectrum triangle, and
its whole geometric-integrality base change before supplying a principal
stage algebra. The original unit witness is the only factorization input. -/
private theorem geometricallyIntegral_baseChange_of_principal_unit
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) (r : R)
    (hr : IsUnit (algebraMap R A r))
    [GeometricallyIntegral (pullback.snd f (Spec.algebraMap R (Localization.Away r)))] :
    GeometricallyIntegral (pullback.snd f (Spec.algebraMap R A)) := by
  let c : Spec (.of A) ⟶ Spec (.of (Localization.Away r)) :=
    Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift r hr :
      Localization.Away r →+* A))
  have hc : c ≫ Spec.algebraMap R (Localization.Away r) = Spec.algebraMap R A := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact IsLocalization.Away.lift_eq r hr x
  exact geometricallyIntegral_baseChange_of_factorization f _ c _ hc

/-- Over a Noetherian domain, the original generic section component is a
clopen with geometrically integral fibres at one actual later principal stage.
The literal original generic preimage and the original section triangle are
retained. No component-locus or geometric-integrality certificate is assumed. -/
theorem exists_principal_geometricallyIntegral_section_component
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K Ω : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n p] [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ p = 𝟙 _) :
    ∃ (s : Finset R⁰) (V : ((baseChangeDiagram R⁰ p).obj (op s)).Opens),
      denominator R⁰ s ≠ 0 ∧
      IsClosed (V : Set ((baseChangeDiagram R⁰ p).obj (op s))) ∧
      baseChangeProjection R⁰ K p (op s) ⁻¹ᵁ V =
        @SmoothSectionComponent.componentOpen K _ _
          (pullback.snd p (Spec.algebraMap R K))
          (MorphismProperty.pullback_snd (P := @Smooth) p (Spec.algebraMap R K)
            (SmoothOfRelativeDimension.smooth n p)) (localizationSection p σ hσ K) ∧
      GeometricallyIntegral (V.ι ≫ pullback.fst (Spec.algebraMap R (stage R⁰ s)) p) ∧
      ∃ τ : Spec (.of (stage R⁰ s)) ⟶ V.toScheme,
        τ ≫ V.ι = principalSection R⁰ p σ hσ (op s) ∧
        τ ≫ V.ι ≫ pullback.fst (Spec.algebraMap R (stage R⁰ s)) p = 𝟙 _ := by
  classical
  let : Smooth p := SmoothOfRelativeDimension.smooth n p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
  obtain ⟨s, V, _, hV, hpre, τ, hτ, _⟩ :=
    exists_principal_genericSectionComponent K p σ hσ
  let b := Spec.algebraMap R (stage R⁰ s)
  let fV := V.ι ≫ (pullback.fst b p ≫ b)
  let i : V.toScheme ⟶ X := V.ι ≫ pullback.snd b p
  let : IsOpenImmersion i := by dsimp only [i, b]; infer_instance
  have hfV : fV = i ≫ p := by
    dsimp only [fV, i]
    rw [Category.assoc, pullback.condition]
  let : SmoothOfRelativeDimension n fV := by
    rw [hfV]
    have h := smoothOfRelativeDimension_comp (n := 0) (m := n) i p
    simpa only [Nat.zero_add] using h
  let : IsClosedImmersion V.ι := .of_isPreimmersion _ (by
    rw [Opens.range_ι]
    exact hV)
  let : QuasiCompact fV := by dsimp only [fV]; infer_instance
  let : QuasiSeparated fV := by dsimp only [fV]; infer_instance
  let : GeometricallyIntegral (pullback.snd fV (Spec.algebraMap R K)) :=
    genericSectionComponent_geometricallyIntegral_generic K p σ hσ s V hpre
  obtain ⟨r, hr, hGI⟩ := exists_ne_zero_geometricallyIntegral_smooth_principal R K Ω fV n
  let r' : R⁰ := ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩
  let t := insert r' s
  let h : op t ⟶ op s := (homOfLE (Finset.subset_insert r' s)).op
  let v := (baseChangeDiagram R⁰ p).map h
  let W := v ⁻¹ᵁ V
  have hrunit : IsUnit (algebraMap R (stage R⁰ t) r) :=
    IsLocalization.Away.isUnit_of_dvd (denominator R⁰ t)
      (Finset.dvd_prod_of_mem (fun a : R⁰ => (a : R)) (Finset.mem_insert_self r' s))
  let : GeometricallyIntegral (pullback.snd fV
      (Spec.algebraMap R (Localization.Away r))) := hGI
  let : GeometricallyIntegral (pullback.snd fV (Spec.algebraMap R (stage R⁰ t))) :=
    geometricallyIntegral_baseChange_of_principal_unit R (stage R⁰ t) fV r hrunit
  have HW : IsPullback (v ∣_ V)
      (W.ι ≫ pullback.fst (Spec.algebraMap R (stage R⁰ t)) p)
      fV (Spec.algebraMap R (stage R⁰ t)) :=
    (isPullback_morphismRestrict v V).paste_vert (stageTransition_isPullback_original R⁰ p h)
  have hWGI : GeometricallyIntegral
      (W.ι ≫ pullback.fst (Spec.algebraMap R (stage R⁰ t)) p) := by
    rw [← HW.isoPullback_hom_snd]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)
      HW.isoPullback.hom _).mpr inferInstance
  have hWpre : baseChangeProjection R⁰ K p (op t) ⁻¹ᵁ W =
      SmoothSectionComponent.componentOpen (pullback.snd p (Spec.algebraMap R K))
        (localizationSection p σ hσ K) := by
    change baseChangeProjection R⁰ K p (op t) ⁻¹ᵁ (v ⁻¹ᵁ V) = _
    rw [← Hom.comp_preimage, (baseChangeCone R⁰ K p).w h, hpre]
  have hτV : principalSection R⁰ p σ hσ (op s) ⁻¹ᵁ V = ⊤ := by
    rw [← hτ, Hom.comp_preimage, Opens.ι_preimage_self, Hom.preimage_top]
  have hτW : principalSection R⁰ p σ hσ (op t) ⁻¹ᵁ W = ⊤ := by
    change principalSection R⁰ p σ hσ (op t) ⁻¹ᵁ (v ⁻¹ᵁ V) = ⊤
    rw [← Hom.comp_preimage, ← principalSection_naturality R⁰ p σ hσ h,
      Hom.comp_preimage, hτV, Hom.preimage_top]
  have hrange : Set.range (principalSection R⁰ p σ hσ (op t)) ⊆ Set.range W.ι := by
    rw [Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change x ∈ principalSection R⁰ p σ hσ (op t) ⁻¹ᵁ W
    rw [hτW]
    trivial
  let τW := IsOpenImmersion.lift W.ι (principalSection R⁰ p σ hσ (op t)) hrange
  have hτWι : τW ≫ W.ι = principalSection R⁰ p σ hσ (op t) :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨t, W, nonZeroDivisors.ne_zero (denominator_mem R⁰ t),
    hV.preimage v.continuous, hWpre, hWGI, τW, hτWι, ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ pullback.fst (Spec.algebraMap R (stage R⁰ t)) p) hτWι).trans
      (principalSection_fst R⁰ p σ hσ (op t)))

end AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
