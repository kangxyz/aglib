/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.TensorCentre

/-! # Identification of the actual selected target centre

The centre induced by the constructed target square is the diagonal-selected
prime, proved using the actual residue comparison and the field embedding.
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

/-- The base DVR acts on the specified residue extension through its residue map. -/
local instance tensorTargetResidueAlgebra : Algebra R E :=
  ((algebraMap (ResidueField R) E).comp (residue R)).toAlgebra

local instance : IsScalarTower R (ResidueField R) E :=
  IsScalarTower.of_algebraMap_eq' rfl

variable {B : Type*} [CommRing B] [Algebra R B]
  (f : B →ₐ[R] E) (g : B →ₐ[R] S)

/-- The literal tensor map into the constructed target DVR. -/
def tensorTarget : B ⊗[R] Ring R E →ₐ[R] TargetRing R E S e :=
  Algebra.TensorProduct.lift
    ((IsScalarTower.toAlgHom R S (TargetRing R E S e)).comp g)
    (targetMap R E S e) (fun _ _ => Commute.all _ _)

@[simp] theorem tensorTarget_tmul (b : B) (a : Ring R E) :
    tensorTarget R E S e g (b ⊗ₜ[R] a) =
      algebraMap S (TargetRing R E S e) (g b) * targetMap R E S e a := rfl

/-- The actual target residue comparison on the left side of the square. -/
@[simp] theorem targetResidueEquiv_residue_left (s : S) :
    targetResidueEquiv R E S e
      (residue (TargetRing R E S e) (algebraMap S (TargetRing R E S e) s)) =
    residue S s := by
  rw [← ResidueField.map_residue, targetResidueEquiv_map]

/-- The actual target residue comparison on the right side of the square. -/
@[simp] theorem targetResidueEquiv_residue_right (a : Ring R E) :
    targetResidueEquiv R E S e
      (residue (TargetRing R E S e) (targetMap R E S e a)) =
    e (localPoint R E a) := by
  change targetResidueEquiv R E S e
    (ResidueField.map (targetMap R E S e).toRingHom (residue (Ring R E) a)) = _
  rw [targetResidueEquiv_rightMap, residueEquiv_residue]

/-- Point compatibility is established on the actual tensor product. -/
theorem tensorTarget_residue (hfg : ∀ b, residue S (g b) = e (f b))
    (x : B ⊗[R] Ring R E) :
    targetResidueEquiv R E S e
      (residue (TargetRing R E S e) (tensorTarget R E S e g x)) =
    e (Algebra.TensorProduct.lmul'' (ResidueField R) (tensorResidue R E f x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul b a =>
      rw [tensorTarget_tmul, map_mul, map_mul,
        targetResidueEquiv_residue_left, targetResidueEquiv_residue_right, hfg,
        tensorResidue_tmul]
      change e (f b) * e (localPoint R E a) = e (f b * localPoint R E a)
      exact (map_mul e _ _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The centre induced by the actual target square is exactly the diagonal-selected prime. -/
theorem tensorTarget_residue_kernel (hfg : ∀ b, residue S (g b) = e (f b)) :
    RingHom.ker ((residue (TargetRing R E S e)).comp
      (tensorTarget R E S e g).toRingHom) =
    SeparableTensorDiagonal.sourceIdeal (ResidueField R) E (tensorResidue R E f) := by
  ext x
  change residue (TargetRing R E S e) (tensorTarget R E S e g x) = 0 ↔
    Algebra.TensorProduct.lmul'' (ResidueField R) (tensorResidue R E f x) = 0
  constructor
  · intro hx
    apply e.injective
    change e (Algebra.TensorProduct.lmul'' (ResidueField R) (tensorResidue R E f x)) = e 0
    rw [← tensorTarget_residue R E S e f g hfg x, hx, map_zero, map_zero]
  · intro hx
    apply (targetResidueEquiv R E S e).injective
    rw [tensorTarget_residue R E S e f g hfg x, hx, map_zero, map_zero]

end SeparableResidueExtension
