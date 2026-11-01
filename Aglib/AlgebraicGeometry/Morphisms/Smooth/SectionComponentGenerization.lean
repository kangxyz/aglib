/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.GenericClopenLift
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.GenericSectionComponentSpreading

/-! # Two original sections and their generic connected component

Over a normal domain, the original generic section component lifts to a
clopen of the original smooth scheme. Connectedness of the base then carries
membership along either original section. This gives the two-section
specialization bridge without a Noetherian or quasi-compactness assumption.
It does not assert relative component openness for arbitrary points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme
open PrincipalNeighborhoodLimit
universe u

/-- If two original sections meet the same connected component of the total
space over one base point, their original generic points belong to the same
connected component of the original generic fibre. -/
theorem generic_sections_mem_connectedComponent_of_mem_connectedComponent
    (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f]
    (σ τ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (hτ : τ ≫ f = 𝟙 _)
    (x : Spec (.of R)) (hx : τ x ∈ connectedComponent (σ x)) :
    localizationSection f τ hτ K (IsLocalRing.closedPoint K) ∈
      connectedComponent (localizationSection f σ hσ K (IsLocalRing.closedPoint K)) := by
  let b := Spec.algebraMap R K
  let q := pullback.snd f b
  let g := pullback.fst f b
  let σK := localizationSection f σ hσ K
  let τK := localizationSection f τ hτ K
  let η := IsLocalRing.closedPoint K
  let U := SmoothSectionComponent.componentOpen q σK
  have hU : IsClosed (U : Set (pullback f b : Scheme.{u})) :=
    SmoothSectionComponent.componentOpen_isClosed q σK
  obtain ⟨V, ⟨hV, hpre⟩, _⟩ :=
    existsUnique_clopen_generic_preimage_of_smooth_normalBase R K f U hU
  have hσg : σK ≫ g = b ≫ σ := pullback.lift_fst _ _ _
  have hτg : τK ≫ g = b ≫ τ := pullback.lift_fst _ _ _
  have hση : σ (b η) ∈ V := by
    have hu := SmoothSectionComponent.mem_componentOpen q σK
    have hv : σK η ∈ g ⁻¹ᵁ V := by rw [hpre]; exact hu
    change g (σK η) ∈ V at hv
    have he := congrArg (fun a : Spec (.of K) ⟶ X => a η) hσg
    change g (σK η) = σ (b η) at he
    exact he ▸ hv
  have hσall : σ ⁻¹' (V : Set X) = Set.univ :=
    (IsClopen.preimage ⟨hV, V.isOpen⟩ σ.continuous).eq_univ ⟨b η, hση⟩
  have hσx : σ x ∈ V := by
    change x ∈ σ ⁻¹' (V : Set X)
    rw [hσall]
    trivial
  have hτx : τ x ∈ V := (IsClopen.connectedComponent_subset ⟨hV, V.isOpen⟩ hσx) hx
  have hτall : τ ⁻¹' (V : Set X) = Set.univ :=
    (IsClopen.preimage ⟨hV, V.isOpen⟩ τ.continuous).eq_univ ⟨x, hτx⟩
  have hτη : τ (b η) ∈ V := by
    change b η ∈ τ ⁻¹' (V : Set X)
    rw [hτall]
    trivial
  have hτU : τK η ∈ U := by
    rw [← hpre]
    change g (τK η) ∈ V
    have he := congrArg (fun a : Spec (.of K) ⟶ X => a η) hτg
    change g (τK η) = τ (b η) at he
    exact he.symm ▸ hτη
  have hcomponent := SmoothSectionComponent.componentOpen_eq_connectedComponent q σK
  change τK η ∈ connectedComponent (σK η)
  rw [← hcomponent]
  exact hτU

/-- A same-component condition in an original scheme-theoretic special fibre
implies the generic condition above, using only the original fibre inclusion. -/
theorem generic_sections_mem_connectedComponent_of_fiber
    (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f]
    (σ τ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (hτ : τ ≫ f = 𝟙 _)
    (x : Spec (.of R))
    (hx : sectionOnFiber f τ hτ x (IsLocalRing.closedPoint ((Spec (.of R)).residueField x)) ∈
      connectedComponent (sectionOnFiber f σ hσ x
        (IsLocalRing.closedPoint ((Spec (.of R)).residueField x)))) :
    localizationSection f τ hτ K (IsLocalRing.closedPoint K) ∈
      connectedComponent (localizationSection f σ hσ K (IsLocalRing.closedPoint K)) := by
  apply generic_sections_mem_connectedComponent_of_mem_connectedComponent R K f σ τ hσ hτ x
  have hh := (f.fiberι x).continuous.mapsTo_connectedComponent
    (sectionOnFiber f σ hσ x
      (IsLocalRing.closedPoint ((Spec (.of R)).residueField x))) hx
  have hs (ρ : Spec (.of R) ⟶ X) (hρ : ρ ≫ f = 𝟙 _) :
      f.fiberι x (sectionOnFiber f ρ hρ x
        (IsLocalRing.closedPoint ((Spec (.of R)).residueField x))) = ρ x := by
    have h := congrArg (fun a => a (IsLocalRing.closedPoint ((Spec (.of R)).residueField x)))
      (sectionOnFiber_fiberι f ρ hρ x)
    change f.fiberι x (sectionOnFiber f ρ hρ x
      (IsLocalRing.closedPoint ((Spec (.of R)).residueField x))) =
      ρ ((Spec (.of R)).fromSpecResidueField x
        (IsLocalRing.closedPoint ((Spec (.of R)).residueField x))) at h
    exact h.trans (congrArg ρ ((Spec (.of R)).fromSpecResidueField_apply x
      (IsLocalRing.closedPoint ((Spec (.of R)).residueField x))))
  rw [hs σ hσ, hs τ hτ] at hh
  exact hh

end AlgebraicGeometry.Scheme
