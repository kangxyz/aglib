/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.WeightedBranches
public import Aglib.FieldTheory.ResidueMinpolyBranch

/-! Norms through the actual minimal-polynomial residue branch. -/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial PolynomialResidue PolynomialNorm Polynomial.LocalResidue AdjoinRoot

attribute [local instance] rootFinite

universe u

/-- The actual residue embedding factors through its literal scalar branch;
the norm contribution is its actual relative residue degree. -/
-- Keep the characteristic-zero base field as part of the finite-extension norm family API.
@[nolint unusedArguments]
theorem finiteExtensionNorm_minpolyScalarBranch
    {k A M V : Type u} [Field k] [CharZero k] [Field A] [Field M] [CharZero M] [Field V]
    [Algebra k A] [Algebra k M] [Algebra M V] [Algebra k V]
    [IsScalarTower k M V] [FiniteDimensional M V]
    (B : PowerBasis k A) (φ : A →ₐ[k] V) (n : ℕ) (x : K A n) :
    finiteExtensionNorm M V n (map n φ.toRingHom x) =
      Module.finrank (IntermediateField.adjoin M {φ B.gen}) V •
        finiteExtensionNorm M
          (AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val) n
          (map n ((adjoinRootMap (algebraMap k M) (minpoly k B.gen)
            (minpolyScalarBranch (M := M) B φ).val.val
            (minpolyScalarBranch (M := M) B φ).property).comp
              (powerBasisMinpolyEquiv B).symm.toRingHom) x) := by
  let q := minpolyScalarBranch (M := M) B φ
  let W := AdjoinRoot q.val.val
  let f := minpolyScalarBranchLift (M := M) B φ
  let : Algebra W V := f.toRingHom.toAlgebra
  let : IsScalarTower M W V := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let : FiniteDimensional W V := FiniteDimensional.right M W V
  let : CharZero W := charZero_of_injective_algebraMap (algebraMap M W).injective
  have hdegree : Module.finrank (IntermediateField.adjoin M {φ B.gen}) V =
      Module.finrank W V := minpolyScalarBranch_finrank B φ
        (minpolyScalarBranchLift_root B φ)
  have hmap : map n φ.toRingHom x = map n (algebraMap W V)
      (map n ((adjoinRootMap (algebraMap k M) (minpoly k B.gen) q.val.val q.property).comp
        (powerBasisMinpolyEquiv B).symm.toRingHom) x) := by
    rw [← LinearMap.comp_apply, ← map_comp]
    have hm := minpolyScalarBranchLift_comp_presentation_symm (M := M) B φ
    change map n φ.toRingHom x = map n
      (f.toRingHom.comp ((adjoinRootMap (algebraMap k M) (minpoly k B.gen)
        q.val.val q.property).comp (powerBasisMinpolyEquiv B).symm.toRingHom)) x
    rw [← RingHom.comp_assoc, hm]
  rw [hmap, finiteExtensionNorm_tower W V, finiteExtensionNorm_map_constants,
    map_smul, natCast_zsmul, hdegree]

open scoped Classical in
/-- The actual minimal-polynomial fiber count gives the weighted residue norm
identity, with the original residue embeddings on every summand. -/
theorem finiteExtensionNorm_restrict_eq_weighted_residue_sum
    {k A M : Type u} [Field k] [CharZero k] [Field A] [Field M] [CharZero M]
    [Algebra k A] [FiniteDimensional k A] [Algebra k M]
    {ι : Type u} [Fintype ι] (V : ι → Type u)
    [∀ i, Field (V i)] [∀ i, Algebra M (V i)] [∀ i, Algebra k (V i)]
    [∀ i, IsScalarTower k M (V i)] [∀ i, FiniteDimensional M (V i)]
    (B : PowerBasis k A) (φ : ∀ i, A →ₐ[k] V i) (b : ι → ℕ) (a : ℕ)
    (hcount : ∀ q : IrreducibleBranch ((minpoly k B.gen).map (algebraMap k M)),
      (∑ i, if minpoly M (φ i B.gen) = q.val.val then
        b i * Module.finrank (IntermediateField.adjoin M {φ i B.gen}) (V i) else 0) = a)
    (n : ℕ) (x : K A n) :
    a • map n (algebraMap k M) (finiteExtensionNorm k A n x) =
      ∑ i, b i • finiteExtensionNorm M (V i) n (map n (φ i).toRingHom x) := by
  classical
  let p : MonicIrreducible k :=
    ⟨minpoly k B.gen, minpoly.monic B.isIntegral_gen, minpoly.irreducible B.isIntegral_gen⟩
  let ε : AdjoinRoot p.val ≃ₐ[k] A := powerBasisMinpolyEquiv B
  let J := IrreducibleBranch (p.val.map (algebraMap k M))
  let : Finite J := finite_irreducibleBranch _ (p.property.1.map _)
  let : Fintype J := Fintype.ofFinite J
  let q : ι → J := fun i => minpolyScalarBranch (M := M) B (φ i)
  let d := fun i => Module.finrank (IntermediateField.adjoin M {φ i B.gen}) (V i)
  let t := fun r : J => finiteExtensionNorm M (AdjoinRoot r.val.val) n
    (map n (adjoinRootMap (algebraMap k M) p.val r.val.val r.property)
      (map n ε.symm.toRingHom x))
  have hindex (i : ι) (r : J) :
      (minpoly M (φ i B.gen) = r.val.val) ↔ q i = r := by
    constructor
    · intro h
      exact Subtype.ext (Subtype.ext h)
    · intro h
      exact congrArg (fun j : J => j.val.val) h
  have hcount' (r : J) : (∑ i, if q i = r then b i * d i else 0) = a := by
    simpa only [hindex] using hcount r
  have hterm (i : ι) : finiteExtensionNorm M (V i) n (map n (φ i).toRingHom x) =
      d i • t (q i) := by
    simpa only [map_comp, LinearMap.comp_apply] using
      finiteExtensionNorm_minpolyScalarBranch B (φ i) n x
  rw [finiteExtensionNorm_eq_presentation k A n p ε, LinearMap.comp_apply,
    polynomialNorm_restrict_branches]
  change a • (∑ r : J, t r) = _
  calc
    a • (∑ r : J, t r) = ∑ r : J, a • t r := Finset.smul_sum
    _ = ∑ r : J, (∑ i, if q i = r then b i * d i else 0) • t r := by
      simp_rw [hcount']
    _ = ∑ i, (b i * d i) • t (q i) := by
      simp_rw [Finset.sum_smul, ite_smul, zero_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single (q i)]
      · simp
      · intro r _ hr
        simp [Ne.symm hr]
      · simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hterm, smul_smul]

end MilnorK
