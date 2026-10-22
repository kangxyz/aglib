/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ChartSections

/-!
# Evaluation through original projective charts

The coordinate calculation is abstract in the ring map into the tensor chart.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial Opposite

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.Segre

variable (R : Type u) [CommRing R] {α : Type u}

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of original chart sections along an arbitrary affine chart ring map. -/
theorem factorChart_pullback_sections (a : α) (B : CommRingCat.{u})
    (c : CommRingCat.of (coordinateRing R α a) ⟶ B)
    (h : ⊤ ≤ (Spec.map c ≫ factorChart R a) ⁻¹ᵁ coordinateOpen R α a) :
    Proj.awayToSection (homogeneousSubmodule α R) (X a) ≫
      (Spec.map c ≫ factorChart R a).appLE (coordinateOpen R α a) ⊤ h =
        c ≫ (Scheme.ΓSpecIso B).inv := by
  have ha : ⊤ ≤ factorChart R a ⁻¹ᵁ coordinateOpen R α a := by
    intro x _
    change factorChart R a x ∈ (coordinateOpen R α a : Set (ProjectiveSpace R α))
    rw [← factorChart_range R a]
    exact ⟨x, rfl⟩
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map c) (factorChart R a)
    (coordinateOpen R α a) ⊤ ⊤ ha le_rfl, ← Category.assoc,
    factorChart_awayToSection]
  change (Scheme.ΓSpecIso _).inv ≫ (Spec.map c).appTop = _
  exact (Scheme.ΓSpecIso_inv_naturality c).symm

set_option backward.isDefEq.respectTransparency false in
/-- A pulled-back original ratio evaluates through the original affine chart square. -/
theorem chart_pullback_ratio {Y : Scheme.{u}} (f : Y ⟶ ProjectiveSpace R α)
    (a k : α) (U : Y.Opens) (hU : U ≤ f ⁻¹ᵁ coordinateOpen R α a)
    (B : CommRingCat.{u}) (j : Spec B ⟶ Y) (hj : ⊤ ≤ j ⁻¹ᵁ U)
    (c : CommRingCat.of (coordinateRing R α a) ⟶ B)
    (hc : j ≫ f = Spec.map c ≫ factorChart R a) :
    (j.appLE U ⊤ hj ≫ (Scheme.ΓSpecIso B).hom) (ratioOn f a k U hU) =
      c (coordinateRatio R α a k) := by
  have ht : ⊤ ≤ (Spec.map c ≫ factorChart R a) ⁻¹ᵁ coordinateOpen R α a := by
    rw [← hc, Scheme.Hom.comp_preimage]
    exact hj.trans ((TopologicalSpace.Opens.map j.base).map (homOfLE hU)).le
  have he := factorChart_pullback_sections R a B c ht
  have ht' : ⊤ ≤ (j ≫ f) ⁻¹ᵁ coordinateOpen R α a :=
    hj.trans ((TopologicalSpace.Opens.map j.base).map (homOfLE hU)).le
  have happ : (Spec.map c ≫ factorChart R a).appLE (coordinateOpen R α a) ⊤ ht =
      (j ≫ f).appLE (coordinateOpen R α a) ⊤ ht' := by
    have aux {v w : Spec B ⟶ ProjectiveSpace R α} (hv : v = w)
        (h₁ : ⊤ ≤ v ⁻¹ᵁ coordinateOpen R α a)
        (h₂ : ⊤ ≤ w ⁻¹ᵁ coordinateOpen R α a) :
        v.appLE (coordinateOpen R α a) ⊤ h₁ = w.appLE (coordinateOpen R α a) ⊤ h₂ := by
      subst w
      rfl
    exact aux hc.symm ht ht'
  rw [happ, ← Scheme.Hom.appLE_comp_appLE j f
    (coordinateOpen R α a) U ⊤ hU hj] at he
  have he' := congrArg (fun t => t ≫ (Scheme.ΓSpecIso B).hom) he
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at he'
  exact ConcreteCategory.congr_hom he' (coordinateRatio R α a k)

end AlgebraicGeometry.ProjectiveSpace.Segre
