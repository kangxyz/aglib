/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.GenericSectionComponentSpreading
public import Aglib.AlgebraicGeometry.Geometrically.Integral.Smooth
public import Aglib.AlgebraicGeometry.Limits.PullbackTransport

/-! # The original generic fibre of a descended section component

A literal preimage equality with the original smooth field component gives
geometric integrality of the original generic fibre of the descended open.
The structural map goes directly to the original base, without choosing a
new fraction-field realization for the principal stage. This lemma does not
assert geometric integrality of the other fibres or relative-locus openness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

universe u

/-- The original descended open has geometrically integral original generic
fibre when its literal generic preimage is the component of the section.
The comparison pastes the existing native squares and preserves the original
fraction-field structural morphism. -/
theorem genericSectionComponent_geometricallyIntegral_generic
    {R : Type u} [CommRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Smooth p]
    (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (s : Finset R⁰) (V : ((baseChangeDiagram R⁰ p).obj (op s)).Opens)
    (hV : baseChangeProjection R⁰ K p (op s) ⁻¹ᵁ V =
      SmoothSectionComponent.componentOpen (pullback.snd p (Spec.algebraMap R K))
        (localizationSection p σ hσ K)) :
    GeometricallyIntegral (pullback.snd
      (V.ι ≫ (pullback.fst (Spec.algebraMap R (stage R⁰ s)) p ≫
        Spec.algebraMap R (stage R⁰ s))) (Spec.algebraMap R K)) := by
  let a := baseChangeProjection R⁰ K p (op s)
  let q := pullback.snd p (Spec.algebraMap R K)
  let o := localizationSection p σ hσ K
  have ho : o ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  let : GeometricallyConnected (SmoothSectionComponent.componentMap q o) :=
    SmoothSectionComponent.componentMap_geometricallyConnected q o ho
  have hcomponent : GeometricallyIntegral ((SmoothSectionComponent.componentOpen q o).ι ≫ q) :=
    geometricallyIntegral_of_smooth_of_geometricallyConnected
      (SmoothSectionComponent.componentMap q o)
  have hpre : GeometricallyIntegral ((a ⁻¹ᵁ V).ι ≫ q) := by
    change a ⁻¹ᵁ V = SmoothSectionComponent.componentOpen q o at hV
    rw [hV]
    exact hcomponent
  let b := Spec.algebraMap R (stage R⁰ s)
  let t := pullback.fst (Spec.algebraMap R (stage R⁰ s)) p ≫ b
  have hbase : Spec.map (CommRingCat.ofHom (projection R⁰ K s)) ≫ b =
      Spec.algebraMap R K := baseStructure_fac R⁰ K (op s)
  have H : IsPullback a q t (Spec.algebraMap R K) := by
    have H₀ := Pullback.Transport.exceptional_intersection_postcompose
      (baseChangeProjection_isPullback R⁰ K p s) b
    simpa only [hbase] using H₀
  have HV : IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ q) (V.ι ≫ t)
      (Spec.algebraMap R K) := (isPullback_morphismRestrict a V).paste_vert H
  have hh : GeometricallyIntegral (HV.isoPullback.hom ≫
      pullback.snd (V.ι ≫ t) (Spec.algebraMap R K)) := by
    rw [HV.isoPullback_hom_snd]
    exact hpre
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)
    HV.isoPullback.hom (pullback.snd (V.ι ≫ t) (Spec.algebraMap R K))).mp hh

end AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
