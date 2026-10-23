/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections
public import Aglib.AlgebraicGeometry.ProjectiveSpace.PulledCoordinates

/-!
# Equality from the original local projective coordinate ratios

The same base triangle and the same pulled original coordinate ratios on
an actual common chart determine the same original projective morphism.
This comparison retains nilpotent sections and uses no field-point reduction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

variable {R I : Type u} [CommRing R] {Y : Scheme.{u}}

/-- The actual chart section-ring homomorphism induced by the original morphism. -/
def chartPullbackRingHom (f : Y ⟶ ProjectiveSpace R I) (a : I)
    (U : Y.Opens) (hU : U ≤ f ⁻¹ᵁ coordinateOpen R I a) :
    coordinateRing R I a →+* Γ(Y, U) :=
  (Proj.awayToSection (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X a) ≫
    f.appLE (coordinateOpen R I a) U hU).hom

@[simp]
theorem chartPullbackRingHom_ratio (f : Y ⟶ ProjectiveSpace R I) (a j : I)
    (U : Y.Opens) (hU : U ≤ f ⁻¹ᵁ coordinateOpen R I a) :
    chartPullbackRingHom f a U hU (coordinateRatio R I a j) = ratioOn f a j U hU := rfl

theorem chartPullbackRingHom_coefficient (f : Y ⟶ ProjectiveSpace R I) (a : I)
    (U : Y.Opens) (hU : U ≤ f ⁻¹ᵁ coordinateOpen R I a) (r : R) :
    chartPullbackRingHom f a U hU (coordinateRingCoefficient R I a r) =
      sectionRestrict Y le_top
        ((f ≫ toSpec R I).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)) := by
  have hc : sectionRestrict (ProjectiveSpace R I) le_top
      ((toSpec R I).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)) =
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X a)).hom
        (coordinateRingCoefficient R I a r) :=
    constant_restriction R I (MvPolynomial.X a) (MvPolynomial.isHomogeneous_X R a)
      Nat.zero_lt_one r
  have hm : (f.appLE (coordinateOpen R I a) U hU)
      (sectionRestrict (ProjectiveSpace R I) le_top
        ((toSpec R I).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))) =
      (f.appLE ⊤ U le_top)
        ((toSpec R I).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)) :=
    ConcreteCategory.congr_hom (f.map_appLE hU (homOfLE le_top).op) _
  calc
    _ = (f.appLE (coordinateOpen R I a) U hU)
        (sectionRestrict (ProjectiveSpace R I) le_top
          ((toSpec R I).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))) :=
      congrArg (f.appLE (coordinateOpen R I a) U hU) hc.symm
    _ = _ := hm
    _ = _ := rfl

/-- The actual native chart ring is determined by its original coefficients and ratios. -/
theorem chartPullbackRingHom_eq (f g : Y ⟶ ProjectiveSpace R I) (a : I)
    (U : Y.Opens) (hf : U ≤ f ⁻¹ᵁ coordinateOpen R I a)
    (hg : U ≤ g ⁻¹ᵁ coordinateOpen R I a)
    (hbase : f ≫ toSpec R I = g ≫ toSpec R I)
    (hratio : ∀ j, ratioOn f a j U hf = ratioOn g a j U hg) :
    chartPullbackRingHom f a U hf = chartPullbackRingHom g a U hg := by
  have h : (chartPullbackRingHom f a U hf).comp (polynomialToCoordinateRing R I a) =
      (chartPullbackRingHom g a U hg).comp (polynomialToCoordinateRing R I a) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, polynomialToCoordinateRing_C,
        chartPullbackRingHom_coefficient, hbase]
    · intro j
      simpa only [RingHom.comp_apply, polynomialToCoordinateRing_X,
        chartPullbackRingHom_ratio] using hratio j.1
  have h' := congrArg (fun φ => φ.comp (coordinateRingToPolynomial R I a)) h
  simpa only [RingHom.comp_assoc, polynomialToCoordinateRing_comp_coordinateRingToPolynomial,
    RingHom.comp_id] using h'

/-- Equality on the original source open follows from the same base triangle
and the same original chart ratios, as equality of actual scheme morphisms. -/
theorem hom_eq_on_open_of_ratios (f g : Y ⟶ ProjectiveSpace R I) (a : I)
    (U : Y.Opens) (hf : U ≤ f ⁻¹ᵁ coordinateOpen R I a)
    (hg : U ≤ g ⁻¹ᵁ coordinateOpen R I a)
    (hbase : f ≫ toSpec R I = g ≫ toSpec R I)
    (hratio : ∀ j, ratioOn f a j U hf = ratioOn g a j U hg) :
    U.ι ≫ f = U.ι ≫ g := by
  let W := coordinateOpen R I a
  let e := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X a)
    (MvPolynomial.isHomogeneous_X R a) Nat.zero_lt_one
  have hring : Proj.awayToSection (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X a) ≫
      f.appLE W U hf =
      Proj.awayToSection (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X a) ≫
        g.appLE W U hg := by
    ext r
    exact RingHom.congr_fun (chartPullbackRingHom_eq f g a U hf hg hbase hratio) r
  have he : f.resLE W U hf ≫ e.hom = g.resLE W U hg ≫ e.hom := by
    apply ext_of_isAffine
    simpa only [Scheme.Hom.comp_appTop, Proj.basicOpenIsoSpec_hom,
      Proj.basicOpenToSpec_app_top, Scheme.Hom.resLE_app_top,
      Category.assoc, Iso.inv_hom_id_assoc, W, e, coordinateOpen] using
        congrArg (fun φ => (Scheme.ΓSpecIso (.of (coordinateRing R I a))).hom ≫
          φ ≫ U.topIso.inv) hring
  have hres := (cancel_mono e.hom).mp he
  calc
    U.ι ≫ f = f.resLE W U hf ≫ W.ι := (Scheme.Hom.resLE_comp_ι f hf).symm
    _ = g.resLE W U hg ≫ W.ι := congrArg (fun φ => φ ≫ W.ι) hres
    _ = U.ι ≫ g := Scheme.Hom.resLE_comp_ι g hg

/-- An actual source open cover with matching original local ratios determines
the same original projective morphism over the same original base. -/
theorem hom_eq_of_cover_ratios {κ : Type u} (U : κ → Y.Opens) (hU : iSup U = ⊤)
    (a : κ → I) (f g : Y ⟶ ProjectiveSpace R I)
    (hf : ∀ k, U k ≤ f ⁻¹ᵁ coordinateOpen R I (a k))
    (hg : ∀ k, U k ≤ g ⁻¹ᵁ coordinateOpen R I (a k))
    (hbase : f ≫ toSpec R I = g ≫ toSpec R I)
    (hratio : ∀ k j, ratioOn f (a k) j (U k) (hf k) =
      ratioOn g (a k) j (U k) (hg k)) : f = g := by
  apply (Y.openCoverOfIsOpenCover U (.mk hU)).hom_ext
  intro k
  exact hom_eq_on_open_of_ratios f g (a k) (U k) (hf k) (hg k) hbase (hratio k)

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
