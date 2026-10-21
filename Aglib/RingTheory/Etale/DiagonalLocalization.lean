/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Unramified.LocalRing

/-! # The selected diagonal localization of a finite separable field extension

Localization of `E ⊗[k] E` at the kernel of multiplication is canonically `E`.
The point is the actual multiplication map, not an unspecified factor of a
product decomposition. This is the local residue calculation for rationalizing
a selected separable centre.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace SeparableTensorDiagonal

variable (k E : Type*) [Field k] [Field E] [Algebra k E]

/-- The prime corresponding to the actual diagonal point. -/
abbrev ideal : Ideal (E ⊗[k] E) :=
  RingHom.ker (Algebra.TensorProduct.lmul'' k : E ⊗[k] E →ₐ[E] E).toRingHom

instance ideal_isPrime : (ideal k E).IsPrime :=
  RingHom.ker_isPrime (Algebra.TensorProduct.lmul'' k : E ⊗[k] E →ₐ[E] E)

/-- The actual localization at the selected diagonal point. -/
abbrev Ring := Localization.AtPrime (ideal k E)

/-- Multiplication extends to the selected localization because every denominator is nonzero. -/
def point : Ring k E →ₐ[E] E :=
  IsLocalization.liftAlgHom (M := (ideal k E).primeCompl)
    (f := Algebra.TensorProduct.lmul'' k) (fun u => by
      apply isUnit_iff_ne_zero.mpr
      exact u.property)

/-- The localized point agrees with the original multiplication map. -/
@[simp] theorem point_algebraMap (x : E ⊗[k] E) :
    point k E (algebraMap (E ⊗[k] E) (Ring k E) x) =
      Algebra.TensorProduct.lmul'' k x :=
  IsLocalization.lift_eq _ x

/-- The left coefficient inclusion is a section of the actual diagonal point. -/
theorem point_coefficient (x : E) :
    point k E (algebraMap E (Ring k E) x) = x := by
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using (point k E).commutes x

/-- The actual diagonal point is surjective, by its coefficient section. -/
theorem point_surjective : Function.Surjective (point k E) :=
  fun x => ⟨algebraMap E (Ring k E) x, point_coefficient k E x⟩

variable [Module.Finite k E] [Algebra.IsSeparable k E]

/-- The selected diagonal local ring is a field by the unramified local criterion. -/
theorem isField_ring : IsField (Ring k E) := by
  let : Algebra.FormallyUnramified k E := Algebra.FormallyUnramified.of_isSeparable k E
  let : Algebra.FormallyUnramified E (E ⊗[k] E) := inferInstance
  let : Algebra.FormallyUnramified E (Ring k E) := inferInstance
  let : Algebra.EssFiniteType E (E ⊗[k] E) := inferInstance
  let : Algebra.EssFiniteType E (Ring k E) := .comp E (E ⊗[k] E) (Ring k E)
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := E) (S := Ring k E)
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot] at hm
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm.symm

/-- Finite separability makes the actual localized point injective. -/
theorem point_injective : Function.Injective (point k E) := by
  let := (isField_ring k E).toField
  exact (point k E).injective

/-- The selected diagonal localization is canonically the original field. -/
def algEquiv : Ring k E ≃ₐ[E] E :=
  AlgEquiv.ofBijective (point k E) ⟨point_injective k E, point_surjective k E⟩

/-- The equivalence is literally multiplication on every original pure tensor. -/
@[simp] theorem algEquiv_tmul (x y : E) :
    algEquiv k E (algebraMap (E ⊗[k] E) (Ring k E) (x ⊗ₜ[k] y)) = x * y := by
  change point k E (algebraMap (E ⊗[k] E) (Ring k E) (x ⊗ₜ[k] y)) = x * y
  rw [point_algebraMap]
  exact Algebra.TensorProduct.lmul'_apply_tmul x y

end SeparableTensorDiagonal
