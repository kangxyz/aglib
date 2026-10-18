/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Embedding
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Primitive-root coordinates of the actual root tensor square

Auxiliary coefficient comparison for K2-018 arithmetic characters and integrality,
mathematical revision e73d98b1b5c1e5abcdebf7d058e436d792b87982, expose SHA256
 e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299.
The source of the embedding is the proved chosen-closure field-restriction module.
Actual n-th-root groups, their natural ZMod n modules, and their literal tensor
square are used below. Neither a root-ratio unit nor its squared effect is a premise.
-/

@[expose] public section

noncomputable section
namespace AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates
open FieldEmbeddingBaseChange Field.absoluteGaloisGroup.CyclotomicCharacter
universe u
variable {F K : Type u} [Field F] [Field K] [CharZero F] [CharZero K]
variable (i : F →+* K) (n : ℕ) [NeZero n]

omit [CharZero K] in
theorem embeddedRoot_primitive : IsPrimitiveRoot (closureEmbedding i (primitiveRoot F n)) n :=
  (primitiveRoot_spec F n).map_of_injective (closureEmbedding i).injective

theorem rootRatio_exists : ∃ a : ℕ, a < n ∧ a.Coprime n ∧
    primitiveRoot K n ^ a = closureEmbedding i (primitiveRoot F n) :=
  (primitiveRoot_spec K n).isPrimitiveRoot_iff.mp (embeddedRoot_primitive i n)

/-- The genuine exponent comparing the embedded global primitive root with the
independently selected local primitive root. -/
def rootExponent : ℕ := (rootRatio_exists i n).choose

theorem rootExponent_lt : rootExponent i n < n := (rootRatio_exists i n).choose_spec.1

theorem rootExponent_coprime : (rootExponent i n).Coprime n :=
  (rootRatio_exists i n).choose_spec.2.1

/-- Primitive-root coordinate change; no root equality is a premise. -/
def rootRatio : (ZMod n)ˣ := ZMod.unitOfCoprime (rootExponent i n) (rootExponent_coprime i n)

theorem rootRatio_spec : primitiveRoot K n ^ (rootRatio i n : ZMod n).val =
    closureEmbedding i (primitiveRoot F n) := by
  rw [rootRatio, ZMod.coe_unitOfCoprime, ZMod.val_natCast,
    Nat.mod_eq_of_lt (rootExponent_lt i n)]
  exact (rootRatio_exists i n).choose_spec.2.2

theorem rootRatio_unique (a : (ZMod n)ˣ)
    (ha : primitiveRoot K n ^ (a : ZMod n).val = closureEmbedding i (primitiveRoot F n)) :
    a = rootRatio i n := by
  apply Units.ext
  apply ZMod.val_injective
  apply (primitiveRoot_spec K n).pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  exact ha.trans (rootRatio_spec i n).symm

/-- The actual embedding on every n-th root, as a multiplicative equivalence. -/
def rootEmbedding : rootsOfUnity n (AlgebraicClosure F) ≃* rootsOfUnity n (AlgebraicClosure K) :=
  rootsOfUnityEquivOfPrimitiveRoots (closureEmbedding i).injective
    ⟨primitiveRoot F n, (mem_primitiveRoots (NeZero.pos n)).mpr (primitiveRoot_spec F n)⟩

omit [CharZero K] in
theorem rootEmbedding_apply (x : rootsOfUnity n (AlgebraicClosure F)) :
    ((rootEmbedding i n x : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      closureEmbedding i (x : (AlgebraicClosure F)ˣ) := by
  rfl

/-- The chosen primitive `n` th root of unity in the algebraic closure of the
characteristic-zero field `F` . -/
def rootUnit (F : Type u) [Field F] [CharZero F] : (AlgebraicClosure F)ˣ :=
  (primitiveRoot_spec F n).toRootsOfUnity

theorem rootUnit_primitive (F : Type u) [Field F] [CharZero F] :
    IsPrimitiveRoot (rootUnit n F) n := IsPrimitiveRoot.coe_units_iff.mp (primitiveRoot_spec F n)

/-- The actual primitive-root basis of the actual root-of-unity group. -/
def rootBasis (F : Type u) [Field F] [CharZero F] :
    Multiplicative (ZMod n) ≃* rootsOfUnity n (AlgebraicClosure F) :=
  ((AddEquiv.toMultiplicative (rootUnit_primitive n F).zmodEquivZPowers).trans
    (MulEquiv.multiplicativeAdditive _)).trans
      (MulEquiv.subgroupCongr (rootUnit_primitive n F).zpowers_eq)

theorem rootBasis_apply (F : Type u) [Field F] [CharZero F] (a : ZMod n) :
    ((rootBasis n F (Multiplicative.ofAdd a) : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) =
      primitiveRoot F n ^ a.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  change (((((rootUnit_primitive n F).zmodEquivZPowers (a.val : ZMod n)).toMul :
    Subgroup.zpowers (rootUnit n F)) : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) = _
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat]
  rfl

theorem rootEmbedding_coordinate (a : ZMod n) :
    rootEmbedding i n (rootBasis n F (Multiplicative.ofAdd a)) =
      rootBasis n K (Multiplicative.ofAdd ((rootRatio i n : ZMod n) * a)) := by
  apply Subtype.ext
  apply Units.ext
  rw [rootEmbedding_apply, rootBasis_apply, map_pow, ← rootRatio_spec, rootBasis_apply, ← pow_mul]
  apply pow_eq_pow_of_modEq _ (primitiveRoot_spec K n).pow_eq_one
  apply (ZMod.natCast_eq_natCast_iff _ _ n).mp
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val]

/-- The additive form of the group of `n` th roots of unity in the algebraic closure of `F` . -/
abbrev RootModule (F : Type u) [Field F] := Additive (rootsOfUnity n (AlgebraicClosure F))

/-- The canonical n-torsion module structure, obtained from root orders. -/
instance rootModule (F : Type u) [Field F] : Module (ZMod n) (RootModule n F) :=
  AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    change x.toMul ^ n = 1
    apply Subtype.ext
    exact x.toMul.property)

/-- Primitive-root coordinates on the actual roots, with their canonical module. -/
def rootCoordinate (F : Type u) [Field F] [CharZero F] : RootModule n F ≃ₗ[ZMod n] ZMod n := by
  let e := (MulEquiv.toAdditive (rootBasis n F).symm).trans (AddEquiv.additiveMultiplicative _)
  exact { e with map_smul' := fun a x => ZMod.map_smul e a x }

/-- Literal map on actual root groups, viewed linearly via their canonical modules. -/
def rootEmbeddingLinear : RootModule n F ≃ₗ[ZMod n] RootModule n K :=
  { MulEquiv.toAdditive (rootEmbedding i n) with
    map_smul' := fun a x => ZMod.map_smul (MulEquiv.toAdditive (rootEmbedding i n)) a x }

theorem rootCoordinate_embedding (x : RootModule n F) :
    rootCoordinate n K (rootEmbeddingLinear i n x) =
      (rootRatio i n : ZMod n) * rootCoordinate n F x := by
  obtain ⟨a, ha⟩ := (rootBasis n F).surjective x.toMul
  have hx : x = Additive.ofMul (rootBasis n F a) := congrArg Additive.ofMul ha.symm
  rw [hx]
  change ((rootBasis n K).symm
      (rootEmbedding i n (rootBasis n F a))).toAdd =
    (rootRatio i n : ZMod n) * ((rootBasis n F).symm (rootBasis n F a)).toAdd
  rw [MulEquiv.symm_apply_apply]
  have h := rootEmbedding_coordinate i n a.toAdd
  change rootEmbedding i n (rootBasis n F a) =
    rootBasis n K (Multiplicative.ofAdd ((rootRatio i n : ZMod n) * a.toAdd)) at h
  rw [h, MulEquiv.symm_apply_apply]
  rfl

/-- The tensor square over `ZMod n` of the additive root-of-unity module of `F` . -/
abbrev RootTensor (F : Type u) [Field F] :=
  TensorProduct (ZMod n) (RootModule n F) (RootModule n F)

/-- The selected root tensor basis. The tensor itself uses the canonical root modules. -/
def tensorCoordinate (F : Type u) [Field F] [CharZero F] : RootTensor n F ≃ₗ[ZMod n] ZMod n :=
  (TensorProduct.congr (rootCoordinate n F) (rootCoordinate n F)).trans
    (TensorProduct.lid (ZMod n) (ZMod n))

/-- The actual tensor-square map is the tensor of the literal root embeddings. -/
def tensorEmbedding : RootTensor n F ≃ₗ[ZMod n] RootTensor n K :=
  TensorProduct.congr (rootEmbeddingLinear i n) (rootEmbeddingLinear i n)

/-- The intrinsic tensor-square embedding is c², where j(ζ_F) = ζ_K^c.
No identity map in independently normalized coordinates is assumed. -/
theorem tensorEmbedding_coordinate (x : RootTensor n F) :
    tensorCoordinate n K (tensorEmbedding i n x) =
      (rootRatio i n : ZMod n)^2 * tensorCoordinate n F x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [tensorEmbedding, tensorCoordinate, LinearEquiv.trans_apply,
      TensorProduct.congr_tmul, TensorProduct.lid_tmul, smul_eq_mul,
      rootCoordinate_embedding]
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy, mul_add]

end AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 3f6c6f6088e647354e7300a70118895bdab337a81ba78779b212d6796b71f204.
Definitions, hypotheses and universes are retained modulo native names. -/
