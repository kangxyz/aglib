/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.TensorOpenResiduePoint
public import Aglib.RingTheory.DiscreteValuationRing.CentreTargetMap

/-! # The actual target-valued point on the finite principal open

The source DVR action on the target is the constructed targetMap. The residue
compatibility uses its native induced residue-field map, not a supplied action.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace SeparableResidueExtension

variable (R E S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field E] [Algebra (ResidueField R) E] [Module.Finite (ResidueField R) E]
  [Algebra.IsSeparable (ResidueField R) E]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)]
  (e : E →ₐ[ResidueField R] ResidueField S)

/-- The base DVR acts on the coefficient field through the specified residue extension. -/
local instance tensorOpenTargetResidueAlgebra : Algebra R E :=
  ((algebraMap (ResidueField R) E).comp (residue R)).toAlgebra

/-- The source DVR acts on the target DVR through the constructed target map. -/
local instance tensorOpenTargetSourceAlgebra : Algebra (Ring R E) (TargetRing R E S e) :=
  (targetMap R E S e).toRingHom.toAlgebra

local instance tensorOpenTargetSourceTower : IsScalarTower R (Ring R E) (TargetRing R E S e) :=
  IsScalarTower.of_algebraMap_eq fun r => (targetMap R E S e).commutes r |>.symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B : Type*} [CommRing B] [Algebra R B]
  (f : B →ₐ[R] E) (g : B →ₐ[R] S)

/-- The actual tensor target map is linear for the actual right source DVR action. -/
def tensorTargetPoint : B ⊗[R] Ring R E →ₐ[Ring R E] TargetRing R E S e where
  toRingHom := (tensorTarget R E S e g).toRingHom
  commutes' a := by
    change tensorTarget R E S e g ((1 : B) ⊗ₜ[R] a) = targetMap R E S e a
    rw [tensorTarget_tmul, map_one, map_one, one_mul]

variable (s : B ⊗[R] Ring R E)
  (hs : s ∉ SeparableTensorDiagonal.sourceIdeal (ResidueField R) E (tensorResidue R E f))
  (hfg : ∀ b, residue S (g b) = e (f b))

/-- The original target point extends to the selected principal open as an actual source-DVR map. -/
def openTargetPoint : Localization.Away s →ₐ[Ring R E] TargetRing R E S e :=
  IsLocalization.Away.liftAlgHom s (f := tensorTargetPoint R E S e g)
    (tensorTarget_denominator_unit R E S e f g hfg ⟨s, hs⟩)

@[simp] theorem openTargetPoint_algebraMap (a : B ⊗[R] Ring R E) :
    openTargetPoint R E S e f g s hs hfg (algebraMap _ (Localization.Away s) a) =
    tensorTarget R E S e g a :=
  IsLocalization.Away.lift_eq s (g := (tensorTargetPoint R E S e g).toRingHom)
    (tensorTarget_denominator_unit R E S e f g hfg ⟨s, hs⟩) a

/-- The native residue-field map of the constructed source-to-target DVR map
is exactly compatible with the actual rational and target points. -/
theorem openTargetPoint_residue (x : Localization.Away s) :
    residue (TargetRing R E S e) (openTargetPoint R E S e f g s hs hfg x) =
      ResidueField.map (targetMap R E S e).toRingHom (openRationalPoint R E f s hs x) := by
  have heq : (residue (TargetRing R E S e)).comp
      (openTargetPoint R E S e f g s hs hfg).toRingHom =
      (ResidueField.map (targetMap R E S e).toRingHom).comp
        (openRationalPoint R E f s hs).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    apply RingHom.ext
    intro a
    change residue (TargetRing R E S e)
      (openTargetPoint R E S e f g s hs hfg (algebraMap _ (Localization.Away s) a)) =
      ResidueField.map (targetMap R E S e).toRingHom
        (openRationalPoint R E f s hs (algebraMap _ (Localization.Away s) a))
    rw [openTargetPoint_algebraMap]
    apply (targetResidueEquiv R E S e).injective
    rw [tensorTarget_residue R E S e f g hfg,
      targetResidueEquiv_rightMap, residueEquiv_openRationalPoint,
      openDiagonalPoint_algebraMap]
    rfl
  exact RingHom.congr_fun heq x

/-- The actual target point retains both sides of the original tensor square. -/
theorem openTargetPoint_tmul (b : B) (a : Ring R E) :
    openTargetPoint R E S e f g s hs hfg
      (algebraMap _ (Localization.Away s) (b ⊗ₜ[R] a)) =
      algebraMap S (TargetRing R E S e) (g b) * targetMap R E S e a := by
  rw [openTargetPoint_algebraMap, tensorTarget_tmul]

end SeparableResidueExtension
