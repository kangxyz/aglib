/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.RootCoordinates

/-!
# Galois actions on roots and their literal tensor square

This is the original root and tensor action construction, retaining its chosen
primitive roots and characteristic-zero hypotheses. The coordinate formula
records the square because both tensor factors carry the root action.
Source: K2-018, revision e73d98b1b5c1e5abcdebf7d058e436d792b87982,
source SHA-256 e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299.
The actual Tate coefficient-fibre identification remains in the application.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TensorActions
open RootCoordinates Field.absoluteGaloisGroup.CyclotomicCharacter
universe u
variable (F : Type u) [Field F] [CharZero F] (n : ℕ) [NeZero n]

/-- The literal absolute-Galois map on actual roots of unity. -/
def rootGalois (σ : Field.absoluteGaloisGroup F) :
    rootsOfUnity n (AlgebraicClosure F) ≃* rootsOfUnity n (AlgebraicClosure F) :=
  rootsOfUnityEquivOfPrimitiveRoots (FieldGalois.asAutomorphism F σ).injective
    ⟨primitiveRoot F n, (mem_primitiveRoots (NeZero.pos n)).mpr (primitiveRoot_spec F n)⟩

theorem rootGalois_apply (σ : Field.absoluteGaloisGroup F) (x : rootsOfUnity n (AlgebraicClosure
  F)) :
    ((rootGalois F n σ x : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) =
      FieldGalois.asAutomorphism F σ (x : (AlgebraicClosure F)ˣ) := rfl

theorem rootGalois_basis (σ : Field.absoluteGaloisGroup F) (a : ZMod n) :
    rootGalois F n σ (rootBasis n F (Multiplicative.ofAdd a)) =
      rootBasis n F (Multiplicative.ofAdd ((character F n σ : ZMod n) * a)) := by
  apply Subtype.ext
  apply Units.ext
  rw [rootGalois_apply, rootBasis_apply, map_pow,
    character_eval F n σ (primitiveRoot F n) (primitiveRoot_spec F n).pow_eq_one,
    rootBasis_apply, ← pow_mul]
  apply pow_eq_pow_of_modEq _ (primitiveRoot_spec F n).pow_eq_one
  apply (ZMod.natCast_eq_natCast_iff _ _ n).mp
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val]

/-- The actual Galois root action is linear for the canonical n-torsion modules. -/
def rootGaloisLinear (σ : Field.absoluteGaloisGroup F) : RootModule n F ≃ₗ[ZMod n] RootModule n F :=
  { MulEquiv.toAdditive (rootGalois F n σ) with
    map_smul' := fun a x => ZMod.map_smul (MulEquiv.toAdditive (rootGalois F n σ)) a x }

theorem rootGalois_coordinate (σ : Field.absoluteGaloisGroup F) (x : RootModule n F) :
    rootCoordinate n F (rootGaloisLinear F n σ x) =
      (character F n σ : ZMod n) * rootCoordinate n F x := by
  obtain ⟨a, ha⟩ := (rootBasis n F).surjective x.toMul
  have hx : x = Additive.ofMul (rootBasis n F a) := congrArg Additive.ofMul ha.symm
  rw [hx]
  change ((rootBasis n F).symm (rootGalois F n σ (rootBasis n F a))).toAdd =
    (character F n σ : ZMod n) * ((rootBasis n F).symm (rootBasis n F a)).toAdd
  rw [MulEquiv.symm_apply_apply]
  have h := rootGalois_basis F n σ a.toAdd
  change rootGalois F n σ (rootBasis n F a) =
    rootBasis n F (Multiplicative.ofAdd ((character F n σ : ZMod n) * a.toAdd)) at h
  rw [h, MulEquiv.symm_apply_apply]
  rfl

/-- The actual tensor-square action is the tensor of actual field automorphisms. -/
def tensorGalois (σ : Field.absoluteGaloisGroup F) : RootTensor n F ≃ₗ[ZMod n] RootTensor n F :=
  TensorProduct.congr (rootGaloisLinear F n σ) (rootGaloisLinear F n σ)

theorem tensorGalois_coordinate (σ : Field.absoluteGaloisGroup F) (x : RootTensor n F) :
    tensorCoordinate n F (tensorGalois F n σ x) =
      (character F n σ : ZMod n)^2 * tensorCoordinate n F x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [tensorGalois, tensorCoordinate, LinearEquiv.trans_apply,
      TensorProduct.congr_tmul, TensorProduct.lid_tmul, smul_eq_mul,
      rootGalois_coordinate]
    ring
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

end AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TensorActions

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 29895e6df89c15e71f7e59867b40582c93d610c9d8d9e25b15045cf7f3e4d3bf.
Definitions, hypotheses and universes are retained modulo native names. -/
