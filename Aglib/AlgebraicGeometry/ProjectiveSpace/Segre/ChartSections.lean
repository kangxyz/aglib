/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ProductChart

/-!
# Section comparison on the original tensor chart

The comparison uses the original open immersion and its native map on sections.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.Segre

variable (R : Type u) [CommRing R] {ι κ : Type u}

set_option backward.isDefEq.respectTransparency false in
/-- Native projective-chart sections pull back to their original localization elements. -/
theorem factorChart_awayToSection {α : Type u} (a : α)
    (h : ⊤ ≤ factorChart R a ⁻¹ᵁ coordinateOpen R α a) :
    Proj.awayToSection (homogeneousSubmodule α R) (X a) ≫
      (factorChart R a).appLE (coordinateOpen R α a) ⊤ h =
        (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing R α a))).inv := by
  let e := Proj.basicOpenIsoSpec (homogeneousSubmodule α R) (X a)
    (isHomogeneous_X R a) Nat.zero_lt_one
  have heTop : e.inv.appLE ⊤ ⊤ le_rfl = e.inv.appTop := by
    simp [Scheme.Hom.appLE]
  have hh : e.hom.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing R α a))).hom ≫
        Proj.awayToSection (homogeneousSubmodule α R) (X a) ≫
          (coordinateOpen R α a).topIso.inv :=
    Proj.basicOpenToSpec_app_top (homogeneousSubmodule α R) (X a)
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing R α a))).hom).mp
  calc
    _ = e.hom.appTop ≫ e.inv.appTop := by
      rw [hh]
      change (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing R α a))).hom ≫
        Proj.awayToSection (homogeneousSubmodule α R) (X a) ≫
          (e.inv ≫ (coordinateOpen R α a).ι).appLE (coordinateOpen R α a) ⊤ h = _
      rw [← Scheme.Hom.appLE_comp_appLE e.inv
        (coordinateOpen R α a).ι (coordinateOpen R α a) ⊤ ⊤
        (coordinateOpen R α a).ι_preimage_self.ge le_rfl]
      rw [heTop]
      simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv, Category.assoc]
      apply congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing R α a))).hom ≫
        Proj.awayToSection (homogeneousSubmodule α R) (X a) ≫ t ≫ e.inv.appTop)
      apply congrArg (ProjectiveSpace R α).presheaf.map
      exact Subsingleton.elim _ _
    _ = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]; simp
    _ = _ := (Iso.hom_inv_id _).symm

/-- The actual section-ring isomorphism of the original product chart. -/
def productSectionsIso (a : ι) (b : κ) :
    Γ(product R ι κ, sourceOpen (first R ι κ) (second R ι κ) (a, b)) ≅
      CommRingCat.of (chartTensor R a b) :=
  (sourceOpen (first R ι κ) (second R ι κ) (a, b)).topIso.symm ≪≫
    Scheme.Γ.mapIso (productOpenIsoSpec R a b).symm.op ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (chartTensor R a b))

set_option backward.isDefEq.respectTransparency false in
/-- The section comparison is the pullback along the unchanged tensor chart. -/
theorem productSectionsIso_hom (a : ι) (b : κ)
    (h : ⊤ ≤ productChart R a b ⁻¹ᵁ
      sourceOpen (first R ι κ) (second R ι κ) (a, b)) :
    (productSectionsIso R a b).hom =
      (productChart R a b).appLE _ ⊤ h ≫
        (Scheme.ΓSpecIso (CommRingCat.of (chartTensor R a b))).hom := by
  let U := sourceOpen (first R ι κ) (second R ι κ) (a, b)
  have ht : ⊤ ≤ ((productOpenIsoSpec R a b).inv ≫ U.ι) ⁻¹ᵁ U := by simp
  have happ : ((productOpenIsoSpec R a b).inv ≫ U.ι).appLE U ⊤ ht =
      (productChart R a b).appLE U ⊤ h := by
    have aux {j k : Spec (CommRingCat.of (chartTensor R a b)) ⟶ product R ι κ}
        (he : j = k) (hj : ⊤ ≤ j ⁻¹ᵁ U) (hk : ⊤ ≤ k ⁻¹ᵁ U) :
        j.appLE U ⊤ hj = k.appLE U ⊤ hk := by subst k; rfl
    exact aux (productOpenIsoSpec_inv_ι R a b) ht h
  rw [← happ]
  rw [← Scheme.Hom.appLE_comp_appLE (productOpenIsoSpec R a b).inv
    (sourceOpen (first R ι κ) (second R ι κ) (a, b)).ι
    (sourceOpen (first R ι κ) (second R ι κ) (a, b)) ⊤ ⊤
    (sourceOpen (first R ι κ) (second R ι κ) (a, b)).ι_preimage_self.ge le_rfl]
  change (U.topIso.inv ≫ (productOpenIsoSpec R a b).inv.appTop) ≫ _ = _
  have heTop : (productOpenIsoSpec R a b).inv.appLE ⊤ ⊤ le_rfl =
      (productOpenIsoSpec R a b).inv.appTop := by simp [Scheme.Hom.appLE]
  rw [heTop]
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  apply congrArg (fun t => (t ≫ (productOpenIsoSpec R a b).inv.appTop) ≫
    (Scheme.ΓSpecIso (CommRingCat.of (chartTensor R a b))).hom)
  apply congrArg (product R ι κ).presheaf.map
  exact Subsingleton.elim _ _

end AlgebraicGeometry.ProjectiveSpace.Segre
