/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.CommonAmbient
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.IsomorphicCharts

/-!
# Actual common refinements with equal ambient data and kernel ideal

The choices are the original base principal refinements, their base
isomorphism, and the original ambient principal refinements followed by
their ambient isomorphism. The original Cartesian squares identify the
source rings and hence the two genuine kernel ideals.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules.Differentials
namespace SmoothClosedImmersionLocalChart

private theorem kernel_comp_iso {A B B' : CommRingCat.{u}} (σ : A ⟶ B) (e : B ≅ B') :
    RingHom.ker (σ ≫ e.hom).hom = RingHom.ker σ.hom := by
  ext z
  change e.hom (σ z) = 0 ↔ σ z = 0
  constructor
  · intro hz
    apply e.commRingCatIsoToRingEquiv.injective
    exact hz.trans (map_zero e.hom.hom).symm
  · intro hz
    rw [hz, map_zero]

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}

/-- The actual common principal and isomorphic refinements have exactly the same
ambient data and generated ideal, with every construction choice retained. -/
theorem exists_canonicalCommonRefinementData
    (C D : SmoothClosedImmersionLocalChart i p n d x) :
    ∃ (r : C.R) (s : D.R)
      (hr : C.σ (C.α r) ∉ C.point.asIdeal)
      (hs : D.σ (D.α s) ∉ D.point.asIdeal)
      (eR : (D.basePrincipalChart s hs).R ≅ (C.basePrincipalChart r hr).R),
      (Spec.map eR.hom ≫ (D.basePrincipalChart s hs).jY =
        (C.basePrincipalChart r hr).jY) ∧
      let C₀ := C.basePrincipalChart r hr
      let D₀ := (D.basePrincipalChart s hs).baseIsoChart eR
      ∃ (a : C₀.A) (b : D₀.A)
        (ha : C₀.σ a ∉ C₀.point.asIdeal) (hb : D₀.σ b ∉ D₀.point.asIdeal)
        (eA : (D₀.principalChart b hb).A ≅ (C₀.principalChart a ha).A),
        (Spec.map eA.hom ≫ (D₀.principalChart b hb).jP =
          (C₀.principalChart a ha).jP) ∧
        let C₁ := C₀.principalChart a ha
        let D₁ := D₀.principalChart b hb
        let D₂ := D₁.ambientIsoChart eA
        C₁.R = D₂.R ∧ C₁.A = D₂.A ∧ HEq C₁.α D₂.α ∧
          HEq C₁.jY D₂.jY ∧ HEq C₁.jP D₂.jP ∧
          HEq (Ideal.ofList C₁.regularList) (Ideal.ofList D₂.regularList) := by
  obtain ⟨r, s, hr, hs, eR, hR⟩ := exists_commonBasePrincipalCharts C D
  refine ⟨r, s, hr, hs, eR, hR, ?_⟩
  let C₀ := C.basePrincipalChart r hr
  let D₀ := (D.basePrincipalChart s hs).baseIsoChart eR
  obtain ⟨a, b, ha, hb, eA, hA⟩ := exists_commonAmbientPrincipalCharts C₀ D₀
  refine ⟨a, b, ha, hb, eA, hA, ?_⟩
  let C₁ := C₀.principalChart a ha
  let D₁ := D₀.principalChart b hb
  let D₂ := D₁.ambientIsoChart eA
  have hY : D₁.jY = C₁.jY := hR
  have hP : D₂.jP = C₁.jP := hA
  have hY₀ : Spec.map (Iso.refl C₁.R).hom ≫ D₁.jY = C₁.jY := by
    simpa only [Iso.refl_hom, Spec.map_id, Category.id_comp] using hY
  have hα₀ := commonAmbientRingSquare C₁ D₁ (Iso.refl C₁.R) eA hY₀ hA
  have hα : C₁.α = D₂.α := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    exact congrArg (fun f : C₁.R ⟶ C₁.A => f z) hα₀
  have hP₀ : Spec.map (Iso.refl C₁.A).hom ≫ D₂.jP = C₁.jP := by
    simpa only [Iso.refl_hom, Spec.map_id, Category.id_comp] using hP
  obtain ⟨eB, _, hσ⟩ := exists_commonSourceRingIso C₁ D₂ (Iso.refl C₁.A) hP₀
  have hσ' : C₁.σ = D₂.σ ≫ eB.hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    exact congrArg (fun f : C₁.A ⟶ C₁.B => f z) hσ
  have hker : RingHom.ker C₁.σ.hom = RingHom.ker D₂.σ.hom := by
    rw [hσ', kernel_comp_iso]
  have hI : Ideal.ofList C₁.regularList = Ideal.ofList D₂.regularList :=
    C₁.kernel.trans (hker.trans D₂.kernel.symm)
  exact ⟨rfl, rfl, heq_of_eq hα, heq_of_eq hY.symm, heq_of_eq hP.symm, heq_of_eq hI⟩

end SmoothClosedImmersionLocalChart
end AlgebraicGeometry.Scheme.Modules.Differentials
