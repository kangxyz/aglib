/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Points.OpenImmersion
public import Aglib.AlgebraicGeometry.Curves.Divisors.Basic

/-! # Restriction and zero-extension of original closed-point divisors

Native finitely supported functions give the two actual divisor maps along
an open immersion into a Jacobson scheme. Restriction is split surjective;
its kernel is exactly the divisors supported on the closed complement. No
principal-divisor or Picard compatibility is asserted by this elementary leaf.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Divisors

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [JacobsonSpace X]

/-- Restrict an original divisor by evaluating at the actual embedded closed points. -/
def openRestriction : Divisor X →+ Divisor U :=
  Finsupp.comapDomain.addMonoidHom (ClosedPoint.openEmbedding j).injective

/-- Extend an original open-subscheme divisor by zero on the complement. -/
def openExtension : Divisor U →+ Divisor X :=
  Finsupp.mapDomain.addMonoidHom (ClosedPoint.openEmbedding j)

/-- Restriction retains the original coefficients at each actual source point. -/
@[simp]
theorem openRestriction_apply (D : Divisor X) (x : ClosedPoint U) :
    openRestriction j D x = D (ClosedPoint.openEmbedding j x) := rfl

/-- Zero-extension retains those same original coefficients. -/
@[simp]
theorem openExtension_apply_image (D : Divisor U) (x : ClosedPoint U) :
    openExtension j D (ClosedPoint.openEmbedding j x) = D x :=
  Finsupp.mapDomain_apply_of_injective (ClosedPoint.openEmbedding j).injective D x

/-- Zero-extension vanishes at every closed point outside the original open image. -/
theorem openExtension_apply_of_not_mem_range (D : Divisor U) (x : ClosedPoint X)
    (hx : x.val ∉ Set.range j) : openExtension j D x = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  exact fun h => hx ((ClosedPoint.mem_range_openEmbedding_iff j x).mp h)

/-- The original divisor restriction has the constructed zero-extension as a section. -/
@[simp]
theorem openRestriction_openExtension (D : Divisor U) :
    openRestriction j (openExtension j D) = D :=
  Finsupp.comapDomain_mapDomain (ClosedPoint.openEmbedding j)
    (ClosedPoint.openEmbedding j).injective D

/-- Every divisor on the open subscheme is the restriction of an actual target divisor. -/
theorem openRestriction_surjective : Function.Surjective (openRestriction j) :=
  fun D => ⟨openExtension j D, openRestriction_openExtension j D⟩

/-- Extension by zero is injective on the original divisor group. -/
theorem openExtension_injective : Function.Injective (openExtension j) :=
  Function.LeftInverse.injective (openRestriction_openExtension j)

/-- The kernel consists exactly of divisors supported outside the original open image. -/
theorem openRestriction_eq_zero_iff (D : Divisor X) :
    openRestriction j D = 0 ↔
      ∀ x ∈ D.support, x.val ∉ Set.range j := by
  constructor
  · intro h x hx hmem
    obtain ⟨y, rfl⟩ := (ClosedPoint.mem_range_openEmbedding_iff j x).mpr hmem
    have hz := DFunLike.congr_fun h y
    exact (Finsupp.mem_support_iff.mp hx) hz
  · intro h
    ext y
    by_contra hy
    exact h (ClosedPoint.openEmbedding j y) (Finsupp.mem_support_iff.mpr hy) ⟨y.val, rfl⟩

/-- A divisor supported in the open image is recovered by restriction and zero-extension. -/
theorem openExtension_openRestriction (D : Divisor X)
    (hD : ∀ x ∈ D.support, x.val ∈ Set.range j) :
    openExtension j (openRestriction j D) = D := by
  apply Finsupp.mapDomain_comapDomain (ClosedPoint.openEmbedding j)
    (ClosedPoint.openEmbedding j).injective D
  intro x hx
  exact (ClosedPoint.mem_range_openEmbedding_iff j x).mpr (hD x hx)

end AlgebraicGeometry.Scheme.OverField.Curve.Divisors
