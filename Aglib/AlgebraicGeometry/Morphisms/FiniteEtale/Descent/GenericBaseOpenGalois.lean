/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GenericFractionGalois
public import Mathlib.AlgebraicGeometry.FunctionField

/-! # Generic Galois covers on actual base opens

The native principal-stage cover is transported to its literal inverse-image
open. The reconstruction isomorphism retains the original generic cover, so
its prescribed point is transported rather than spread as a new point.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

/-- The original inverse-image open is connected over a nonempty base open. -/
theorem baseOpen_connected (R : Type u) [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Smooth p]
    [GeometricallyConnected p] (W : (Spec (.of R)).Opens) [Nonempty W] :
    ConnectedSpace (p ⁻¹ᵁ W : X.Opens) :=
  GeometricallyConnected.connectedSpace (p ∣_ W) (p ∣_ W).isOpenMap

/-- A generic Galois cover extends to the literal inverse image of an actual
nonempty base open, preserving its original reconstruction and deck order. -/
theorem exists_fraction_baseOpen_galois_cover
    (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (p : X ⟶ Spec (.of R)) [Smooth p] [GeometricallyConnected p]
    (Y : FiniteEtale (pullback p (Spec.algebraMap R K))) [IsGalois Y] :
    ∃ (W : (Spec (.of R)).Opens) (hW : Nonempty W),
      let : Nonempty W := hW
      let : ConnectedSpace (p ⁻¹ᵁ W : X.Opens) := baseOpen_connected R p W
      ∃ (E : FiniteEtale (p ⁻¹ᵁ W))
      (g : pullback p (Spec.algebraMap R K) ⟶ (p ⁻¹ᵁ W : X.Opens)),
      g ≫ (p ⁻¹ᵁ W).ι = pullback.fst p (Spec.algebraMap R K) ∧
      IsIntegral E.obj.left ∧ IsGalois E ∧
      Nat.card (Aut E) = Nat.card (Aut Y) ∧ Nonempty ((baseChange g).obj E ≅ Y) := by
  classical
  let : ConnectedSpace (pullback p (Spec.algebraMap R K) : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (pullback.snd p (Spec.algebraMap R K))
  obtain ⟨t, C, hC, hG, hcard, ⟨e⟩⟩ := exists_principal_galois_cover R K p Y
  let := hC
  let := hG
  let W := stageBaseOpen R⁰ t
  let U := stageSourceOpen R⁰ p t
  let i : (PrincipalNeighborhoodLimit.baseChangeDiagram R⁰ p).obj (op t) ≅ U :=
    stageOpenIso R⁰ p t
  let b := PrincipalNeighborhoodLimit.baseChangeProjection R⁰ K p (op t)
  let g : pullback p (Spec.algebraMap R K) ⟶ U := b ≫ i.hom
  let E := (baseChange i.inv).obj C
  let : Nonempty ((PrincipalNeighborhoodLimit.baseChangeDiagram R⁰ p).obj (op t)) :=
    Nonempty.map C.obj.hom (inferInstance : Nonempty C.obj.left)
  let : ConnectedSpace ((PrincipalNeighborhoodLimit.baseChangeDiagram R⁰ p).obj (op t)) :=
    GeometricallyConnected.connectedSpace
      (pullback.fst (Spec.algebraMap R (stage R⁰ t)) p)
      (pullback.fst (Spec.algebraMap R (stage R⁰ t)) p).isOpenMap
  let : ConnectedSpace U := i.hom.homeomorph.connectedSpace_iff.mp inferInstance
  let : IsIntegral E.obj.left :=
    IsIntegral.of_isIso (inv (pullback.fst C.obj.hom i.inv))
  let : IsGalois E := baseChange_isGalois_of_connected i.inv C
  have hg : g ≫ U.ι = pullback.fst p (Spec.algebraMap R K) := by
    dsimp only [g, i, U]
    rw [Category.assoc, stageOpenIso_hom_over, baseChangeProjection_base]
  have hb : g ≫ i.inv = b := by simp only [g, Category.assoc, i.hom_inv_id, Category.comp_id]
  let e' : (baseChange g).obj E ≅ Y :=
    ((baseChangeComp i.inv g).app C).symm ≪≫
      (eqToIso (congrArg (fun f => (baseChange f).obj C) hb)) ≪≫ e
  have hW : Nonempty W := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨⟨p (U.ι x), x.property⟩⟩
  exact ⟨W, hW, E, g, hg, inferInstance, inferInstance,
    (baseChange_card_aut_of_connected i.inv C).trans hcard, ⟨e'⟩⟩

/-- Transport the whole original cover family along an equality of base arrows.
The connectedness instance is bound over that same arrow before transport. -/
theorem exists_fraction_baseOpen_galois_cover_of_eq
    (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (p : X ⟶ Spec (.of R)) [Smooth p] [GeometricallyConnected p]
    (γ : Spec (.of K) ⟶ Spec (.of R)) (hγ : γ = Spec.algebraMap R K)
    [ConnectedSpace (pullback p γ : Scheme.{u})]
    (Y : FiniteEtale (pullback p γ)) [IsGalois Y] :
    ∃ (W : (Spec (.of R)).Opens) (hW : Nonempty W),
      let : Nonempty W := hW
      let : ConnectedSpace (p ⁻¹ᵁ W : X.Opens) := baseOpen_connected R p W
      ∃ (E : FiniteEtale (p ⁻¹ᵁ W))
      (g : pullback p γ ⟶ (p ⁻¹ᵁ W : X.Opens)),
      g ≫ (p ⁻¹ᵁ W).ι = pullback.fst p γ ∧
      IsIntegral E.obj.left ∧ IsGalois E ∧
      Nat.card (Aut E) = Nat.card (Aut Y) ∧ Nonempty ((baseChange g).obj E ≅ Y) := by
  subst γ
  exact exists_fraction_baseOpen_galois_cover R K p Y

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (.of R)) [Smooth p] [GeometricallyConnected p]

local instance originalGeneric_connected :
    ConnectedSpace (pullback p
      ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R)))) : Scheme.{u}) := by
  let f : pullback p
      ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R)))) ⟶
      Spec (Spec (.of R)).functionField := pullback.snd p _
  let : Subsingleton (Spec (Spec (.of R)).functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (Spec (.of R)).functionField))
  exact GeometricallyConnected.connectedSpace_of_subsingleton f

/-- The original function-field cover descends to an actual base open.
The function field and the generic-point map are the original stalk objects. -/
theorem exists_generic_baseOpen_galois_cover
    (Y : FiniteEtale (pullback p
      ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R)))))) [IsGalois Y] :
    ∃ (W : (Spec (.of R)).Opens) (hW : Nonempty W),
      let : Nonempty W := hW
      let : ConnectedSpace (p ⁻¹ᵁ W : X.Opens) := baseOpen_connected R p W
      ∃ (E : FiniteEtale (p ⁻¹ᵁ W))
      (g : pullback p ((Spec (.of R)).fromSpecStalk
        (genericPoint (Spec (.of R)))) ⟶ (p ⁻¹ᵁ W : X.Opens)),
      g ≫ (p ⁻¹ᵁ W).ι = pullback.fst p _ ∧
      IsIntegral E.obj.left ∧ IsGalois E ∧
      Nat.card (Aut E) = Nat.card (Aut Y) ∧ Nonempty ((baseChange g).obj E ≅ Y) := by
  let : Algebra R (Spec (.of R)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  let : IsFractionRing R (Spec (.of R)).functionField :=
    functionField_isFractionRing_of_affine (.of R)
  have hγ : (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) =
      Spec.algebraMap R (Spec (.of R)).functionField :=
    Spec.fromSpecStalk_eq' (.of R) (genericPoint (Spec (.of R)))
  exact exists_fraction_baseOpen_galois_cover_of_eq R (Spec (.of R)).functionField p
    ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R)))) hγ Y

/-- A prescribed original generic point is transported through the same
reconstruction. No second point or field of definition is chosen. -/
theorem exists_generic_baseOpen_galois_point
    (s : Spec (.of R) ⟶ X)
    (Y : FiniteEtale (pullback p
      ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R)))))) [IsGalois Y]
    (a : Spec (Spec (.of R)).functionField ⟶ Y.obj.left)
    (ha : a ≫ Y.obj.hom ≫ pullback.fst p _ =
      (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ s) :
    ∃ (W : (Spec (.of R)).Opens) (hW : Nonempty W),
      let : Nonempty W := hW
      let : ConnectedSpace (p ⁻¹ᵁ W : X.Opens) := baseOpen_connected R p W
      ∃ (E : FiniteEtale (p ⁻¹ᵁ W))
      (g : pullback p ((Spec (.of R)).fromSpecStalk
        (genericPoint (Spec (.of R)))) ⟶ (p ⁻¹ᵁ W : X.Opens)),
      g ≫ (p ⁻¹ᵁ W).ι = pullback.fst p _ ∧
      IsIntegral E.obj.left ∧ IsGalois E ∧ Nat.card (Aut E) = Nat.card (Aut Y) ∧
      ∃ e : (baseChange g).obj E ≅ Y,
        ∃ aW : Spec (Spec (.of R)).functionField ⟶ E.obj.left,
          aW = a ≫ e.inv.hom.left ≫ pullback.fst E.obj.hom g ∧
          aW ≫ E.obj.hom ≫ (p ⁻¹ᵁ W).ι =
            (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ s := by
  obtain ⟨W, hW, E, g, hg, hI, hG, hc, ⟨e⟩⟩ :=
    exists_generic_baseOpen_galois_cover R p Y
  refine ⟨W, hW, E, g, hg, hI, hG, hc, e,
    a ≫ e.inv.hom.left ≫ pullback.fst E.obj.hom g, rfl, ?_⟩
  let eX : Y.obj.left ⟶ pullback E.obj.hom g := e.inv.hom.left
  have he : eX ≫ pullback.snd E.obj.hom g = Y.obj.hom := Over.w e.inv.hom
  change (a ≫ eX ≫ pullback.fst E.obj.hom g) ≫ E.obj.hom ≫ (p ⁻¹ᵁ W).ι = _
  rw [Category.assoc, Category.assoc, ← Category.assoc (pullback.fst _ _),
    pullback.condition, Category.assoc, hg, ← Category.assoc eX, he]
  exact ha

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
