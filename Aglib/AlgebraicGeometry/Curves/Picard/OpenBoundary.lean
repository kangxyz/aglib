/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.OpenClasses
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.Algebra.Group.Subgroup.KernelSquare
public import Mathlib.Algebra.Group.Units.Equiv

/-! # The original Picard restriction kernel and boundary divisors

The original principal-divisor kernels, the actual open-immersion map on
function-field units, and the native subgroup kernel-square construction
identify the original Picard pullback kernel with boundary divisor classes.
This is a Picard statement, not a cohomological residue or localization
sequence. No power-surjectivity of affine global units is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

section Principal

variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
  (hdim : topologicalKrullDim X ≤ 1)

/-- The constructed original divisor-class map has exactly the original
principal divisors as its kernel. -/
theorem divisorToPicard_ker : (divisorToPicard X hdim).ker = (principal X).range := by
  ext D
  change divisorPicardEquiv X hdim (QuotientAddGroup.mk D) = 0 ↔ _
  rw [← (divisorPicardEquiv X hdim).map_zero,
    (divisorPicardEquiv X hdim).injective.eq_iff, QuotientAddGroup.eq_zero_iff]

/-- Every original Picard class has a divisor representative, using the
already constructed divisor/Picard equivalence. -/
theorem divisorToPicard_surjective : Function.Surjective (divisorToPicard X hdim) := by
  intro a
  obtain ⟨b, rfl⟩ := (divisorPicardEquiv X hdim).surjective a
  induction b using Quotient.inductionOn with
  | h D => exact ⟨D, rfl⟩

end Principal

variable {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
  [IsNoetherian U] [IsNoetherian X] [JacobsonSpace X]
  [∀ x : ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk x.val)]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
  (j : U ⟶ X) [IsOpenImmersion j]

local instance : IsDominant j := Scheme.isDominant_of_isOpenImmersion j

/-- Original principal divisors on the open are restrictions of original
principal divisors, because the actual function-field map is an equivalence. -/
theorem principal_range_map_openRestriction :
    (principal X).range.map (openRestriction j) = (principal U).range := by
  have hu : Function.Surjective (Scheme.functionFieldUnitMap j) :=
    (Units.mapEquiv (Scheme.FunctionField.fieldEquiv j).toMulEquiv).surjective
  ext E
  constructor
  · rintro ⟨D, ⟨f, rfl⟩, rfl⟩
    exact ⟨Additive.ofMul (Scheme.functionFieldUnitMap j f.toMul),
      (openRestriction_principal j f.toMul).symm⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := hu f.toMul
    refine ⟨principal X (Additive.ofMul g), ⟨Additive.ofMul g, rfl⟩, ?_⟩
    rw [openRestriction_principal, hg]
    rfl

/-- The kernel of the original additive Picard pullback is precisely the
image of the original divisors supported on the boundary. -/
theorem pullbackHom_openImmersion_ker (hdim : topologicalKrullDim X ≤ 1) :
    (PullbackTensor.Local.pullbackHom j).ker =
      (openRestriction j).ker.map (divisorToPicard X hdim) := by
  symm
  apply AddMonoidHom.map_ker_eq_of_surjective_square
    (divisorToPicard X hdim)
    (divisorToPicard U (openSource_dimension_le_one j hdim))
    (openRestriction j) (PullbackTensor.Local.pullbackHom j)
    (divisorToPicard_surjective X hdim)
  · apply AddMonoidHom.ext
    intro D
    exact pullbackClass_divisor j hdim D
  · rw [divisorToPicard_ker, divisorToPicard_ker]
    exact principal_range_map_openRestriction j

/-- A class restricts to zero exactly when it is represented by an original
divisor whose finite support lies outside the original open image. -/
theorem pullbackClass_eq_zero_iff_boundary (hdim : topologicalKrullDim X ≤ 1)
    (a : PicardGroup X) :
    pullbackClass j a = 0 ↔ ∃ D : Divisor X,
      (∀ x ∈ D.support, x.val ∉ Set.range j) ∧
      classOf X (divisorLineBundle X hdim D) = a := by
  change a ∈ (PullbackTensor.Local.pullbackHom j).ker ↔ _
  rw [pullbackHom_openImmersion_ker j hdim]
  constructor
  · rintro ⟨D, hD, ha⟩
    exact ⟨D, (openRestriction_eq_zero_iff j D).mp hD, ha⟩
  · rintro ⟨D, hD, ha⟩
    exact ⟨D, (openRestriction_eq_zero_iff j D).mpr hD, ha⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
