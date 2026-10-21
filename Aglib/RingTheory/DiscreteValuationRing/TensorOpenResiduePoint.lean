/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.TensorFiniteOpen

/-! # The actual rational residue point on a finite principal open -/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace SeparableResidueExtension

variable (R E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field E] [Algebra (ResidueField R) E] [Module.Finite (ResidueField R) E]
  [Algebra.IsSeparable (ResidueField R) E]

/-- The base DVR acts on the rational residue field through its specified residue extension. -/
local instance tensorOpenResidueBaseAlgebra : Algebra R E :=
  ((algebraMap (ResidueField R) E).comp (residue R)).toAlgebra

/-- The constructed source DVR acts on the residue field through its actual local point. -/
local instance tensorOpenResidueSourceAlgebra :
    Algebra (Ring R E) E := (localPoint R E).toRingHom.toAlgebra

/-- The existing residue comparison, now over the actual source DVR itself. -/
def localResidueAlgEquiv : ResidueField (Ring R E) ≃ₐ[Ring R E] E where
  __ := residueEquiv R E
  commutes' a := residueEquiv_residue R E a

variable {B : Type*} [CommRing B] [Algebra R B] (f : B →ₐ[R] E)

/-- The tensor algebra carries the action of its right-hand source DVR. -/
local instance tensorOpenResidueRightAlgebra : Algebra (Ring R E) (B ⊗[R] Ring R E) :=
  Algebra.TensorProduct.rightAlgebra

/-- Multiplication after the actual tensor quotient is linear over the right source DVR. -/
def tensorDiagonalPoint : B ⊗[R] Ring R E →ₐ[Ring R E] E where
  toRingHom := (Algebra.TensorProduct.lmul'' (ResidueField R) (S := E)).toRingHom.comp
    (tensorResidue R E f)
  commutes' a := by
    change Algebra.TensorProduct.lmul'' (ResidueField R) (S := E)
      (tensorResidue R E f ((1 : B) ⊗ₜ[R] a)) = localPoint R E a
    rw [tensorResidue_tmul, map_one]
    exact one_mul _

@[simp] theorem tensorDiagonalPoint_tmul (b : B) (a : Ring R E) :
    tensorDiagonalPoint R E f (b ⊗ₜ[R] a) = f b * localPoint R E a := rfl

variable (s : B ⊗[R] Ring R E)
  (hs : s ∉ SeparableTensorDiagonal.sourceIdeal (ResidueField R) E (tensorResidue R E f))

/-- The actual diagonal residue point extends to the selected principal open. -/
def openDiagonalPoint : Localization.Away s →ₐ[Ring R E] E :=
  IsLocalization.Away.liftAlgHom s (f := tensorDiagonalPoint R E f)
    (isUnit_iff_ne_zero.mpr hs)

@[simp] theorem openDiagonalPoint_algebraMap (a : B ⊗[R] Ring R E) :
    openDiagonalPoint R E f s hs (algebraMap _ (Localization.Away s) a) =
    tensorDiagonalPoint R E f a :=
  IsLocalization.Away.lift_eq s
    (g := (tensorDiagonalPoint R E f).toRingHom) (isUnit_iff_ne_zero.mpr hs) a

/-- The actual point remains surjective after restricting to the principal open. -/
theorem openDiagonalPoint_surjective (hf : Function.Surjective f) :
    Function.Surjective (openDiagonalPoint R E f s hs) := by
  intro x
  obtain ⟨b, hb⟩ := hf x
  refine ⟨algebraMap _ (Localization.Away s) (b ⊗ₜ[R] (1 : Ring R E)), ?_⟩
  rw [openDiagonalPoint_algebraMap, tensorDiagonalPoint_tmul, hb, map_one, mul_one]

/-- The kernel is exactly the extension of the actual diagonal centre ideal. -/
theorem ker_openDiagonalPoint :
    RingHom.ker (openDiagonalPoint R E f s hs).toRingHom =
      (SeparableTensorDiagonal.sourceIdeal (ResidueField R) E (tensorResidue R E f)).map
        (algebraMap (B ⊗[R] Ring R E) (Localization.Away s)) := by
  have hker : (RingHom.ker (openDiagonalPoint R E f s hs).toRingHom).under
      (B ⊗[R] Ring R E) =
      SeparableTensorDiagonal.sourceIdeal (ResidueField R) E (tensorResidue R E f) := by
    ext a
    change openDiagonalPoint R E f s hs (algebraMap _ (Localization.Away s) a) = 0 ↔ _
    rw [openDiagonalPoint_algebraMap]
    rfl
  rw [← hker]
  exact (IsLocalization.map_under (Submonoid.powers s) (Localization.Away s)
    (RingHom.ker (openDiagonalPoint R E f s hs).toRingHom)).symm

/-- The native source-residue-field-valued rational point, not an assumed residue model. -/
def openRationalPoint : Localization.Away s →ₐ[Ring R E] ResidueField (Ring R E) :=
  (localResidueAlgEquiv R E).symm.toAlgHom.comp (openDiagonalPoint R E f s hs)

@[simp] theorem residueEquiv_openRationalPoint (x : Localization.Away s) :
    residueEquiv R E (openRationalPoint R E f s hs x) = openDiagonalPoint R E f s hs x :=
  (residueEquiv R E).apply_symm_apply _

/-- The actual rational point is surjective. -/
theorem openRationalPoint_surjective (hf : Function.Surjective f) :
    Function.Surjective (openRationalPoint R E f s hs) :=
  (localResidueAlgEquiv R E).symm.surjective.comp (openDiagonalPoint_surjective R E f s hs hf)

/-- Transport to the native source residue field does not change the actual kernel. -/
theorem ker_openRationalPoint :
    RingHom.ker (openRationalPoint R E f s hs).toRingHom =
      (SeparableTensorDiagonal.sourceIdeal (ResidueField R) E (tensorResidue R E f)).map
        (algebraMap (B ⊗[R] Ring R E) (Localization.Away s)) := by
  rw [← ker_openDiagonalPoint R E f s hs]
  ext x
  constructor
  · intro hx
    change openRationalPoint R E f s hs x = 0 at hx
    change openDiagonalPoint R E f s hs x = 0
    have hh := congrArg (residueEquiv R E) hx
    simpa only [residueEquiv_openRationalPoint, map_zero] using hh
  · intro hx
    change (residueEquiv R E).symm (openDiagonalPoint R E f s hs x) = 0
    rw [show openDiagonalPoint R E f s hs x = 0 from hx, map_zero]

end SeparableResidueExtension
