/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.SectionExtension
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Constants

/-!
# Original projective coordinates on arbitrary source subopens

The functions are evaluated by the native `appLE`, with the actual source-open
inclusion. The ratio cocycle is proved before specializing to a product scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MvPolynomial
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable {R : Type u} [CommRing R] {α : Type u} {Y : Scheme.{u}}
  (f : Y ⟶ ProjectiveSpace R α)

/-- The original coordinate ratio pulled back to any source subopen. -/
def ratioOn (a i : α) (U : Y.Opens) (hU : U ≤ f ⁻¹ᵁ coordinateOpen R α a) : Γ(Y, U) :=
  (f.appLE (coordinateOpen R α a) U hU) (coordinateRatioSection R α a i)

@[simp]
theorem ratioOn_self (a : α) (U : Y.Opens) (hU : U ≤ f ⁻¹ᵁ coordinateOpen R α a) :
    ratioOn f a a U hU = 1 := by
  simp [ratioOn]

@[simp]
theorem ratioOn_restrict (a i : α) {U V : Y.Opens} (h : V ≤ U)
    (hU : U ≤ f ⁻¹ᵁ coordinateOpen R α a) :
    sectionRestrict Y h (ratioOn f a i U hU) = ratioOn f a i V (h.trans hU) := by
  exact ConcreteCategory.congr_hom (f.appLE_map hU (homOfLE h).op)
    (coordinateRatioSection R α a i)

/-- The basic open of a pulled-back original ratio is exactly the source open
intersected with the other original coordinate chart. -/
theorem basicOpen_ratioOn (a i : α) (U : Y.Opens)
    (hU : U ≤ f ⁻¹ᵁ coordinateOpen R α a) :
    Y.basicOpen (ratioOn f a i U hU) = U ⊓ f ⁻¹ᵁ coordinateOpen R α i := by
  change Y.basicOpen (Y.presheaf.map (homOfLE hU).op
    ((f.app (coordinateOpen R α a)) (coordinateRatioSection R α a i))) = _
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen,
    basicOpen_coordinateRatioSection, Scheme.Hom.preimage_inf, ← inf_assoc,
    inf_eq_left.mpr hU]

/-- Native factor-chart ratios satisfy the multiplicative cocycle on every
common target subopen. -/
theorem coordinateRatioSection_mul (a b k : α)
    {V : (ProjectiveSpace R α).Opens} (ha : V ≤ coordinateOpen R α a)
    (hb : V ≤ coordinateOpen R α b) :
    sectionRestrict (ProjectiveSpace R α) ha (coordinateRatioSection R α a k) =
      sectionRestrict (ProjectiveSpace R α) ha (coordinateRatioSection R α a b) *
        sectionRestrict (ProjectiveSpace R α) hb (coordinateRatioSection R α b k) := by
  have hk := coordinateRatioSection_transition_mul R α k a b ha hb
  have hb' := coordinateRatioSection_transition_mul R α b a b ha hb
  simp only [coordinateRatioSection_self, map_one] at hb'
  rw [hk, ← mul_assoc,
    mul_comm (sectionRestrict (ProjectiveSpace R α) ha (coordinateRatioSection R α a b)),
    ← hb', one_mul]

/-- The ratio cocycle is preserved by the actual source map on arbitrary
source subopens; no affine or finite-type hypothesis occurs. -/
theorem ratioOn_mul (a b k : α) (U : Y.Opens)
    (ha : U ≤ f ⁻¹ᵁ coordinateOpen R α a)
    (hb : U ≤ f ⁻¹ᵁ coordinateOpen R α b) :
    ratioOn f a k U ha = ratioOn f a b U ha * ratioOn f b k U hb := by
  let V := coordinateOpen R α a ⊓ coordinateOpen R α b
  have hU : U ≤ f ⁻¹ᵁ V := by
    rw [Scheme.Hom.preimage_inf]
    exact le_inf ha hb
  have hmapa (s : Γ(ProjectiveSpace R α, coordinateOpen R α a)) :
      (f.appLE V U hU) (sectionRestrict (ProjectiveSpace R α) inf_le_left s) =
        (f.appLE (coordinateOpen R α a) U ha) s :=
    ConcreteCategory.congr_hom (f.map_appLE hU (homOfLE inf_le_left).op) s
  have hmapb (s : Γ(ProjectiveSpace R α, coordinateOpen R α b)) :
      (f.appLE V U hU) (sectionRestrict (ProjectiveSpace R α) inf_le_right s) =
        (f.appLE (coordinateOpen R α b) U hb) s :=
    ConcreteCategory.congr_hom (f.map_appLE hU (homOfLE inf_le_right).op) s
  have h := congrArg (f.appLE V U hU)
    (coordinateRatioSection_mul (R := R) a b k
      (inf_le_left : V ≤ coordinateOpen R α a) inf_le_right)
  simpa only [map_mul, hmapa, hmapb, ratioOn] using h

end AlgebraicGeometry.ProjectiveSpace
