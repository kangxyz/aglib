/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootScalarBranches
public import Aglib.FieldTheory.AdjoinRootMinpolyDegree

/-!
# Actual residue embeddings select literal minimal-polynomial branches

A primitive residue presentation and the original residue embedding determine a
literal scalar branch. Evaluation of its quotient root preserves both original
coefficient maps and recovers the original residue embedding on every class.
-/

@[expose] public noncomputable section

open Polynomial Polynomial.LocalResidue

namespace AdjoinRoot

variable {k A M V : Type*} [Field k] [Field A] [Field M] [Field V]
  [Algebra k A] [Algebra k M] [Algebra M V] [Algebra k V]
  [IsScalarTower k M V] [FiniteDimensional M V]

/-- The primitive field is presented by its original power-basis minimal polynomial. -/
def powerBasisMinpolyEquiv (B : PowerBasis k A) :
    AdjoinRoot (minpoly k B.gen) ≃ₐ[k] A :=
  equiv' (minpoly k B.gen) B
    (by rw [aeval_eq, mk_self]) (minpoly.aeval k B.gen)

@[simp]
theorem powerBasisMinpolyEquiv_root (B : PowerBasis k A) :
    powerBasisMinpolyEquiv B (root (minpoly k B.gen)) = B.gen := by
  change liftAlgHom (minpoly k B.gen) (Algebra.ofId k A) B.gen
    (minpoly.aeval k B.gen) (root (minpoly k B.gen)) = B.gen
  exact liftAlgHom_root _ _ _ _

/-- The selected branch is literally the minimal polynomial of the image of
the original primitive generator. -/
def minpolyScalarBranch (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    IrreducibleBranch ((minpoly k B.gen).map (algebraMap k M)) := by
  refine ⟨⟨minpoly M (φ B.gen), minpoly.monic (Algebra.IsIntegral.isIntegral _),
    minpoly.irreducible (Algebra.IsIntegral.isIntegral _)⟩, ?_⟩
  apply minpoly.dvd M (φ B.gen)
  rw [Polynomial.aeval_map_algebraMap M, Polynomial.aeval_algHom_apply,
    minpoly.aeval, map_zero]

@[simp]
theorem minpolyScalarBranch_val (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    (minpolyScalarBranch (M := M) B φ).val.val = minpoly M (φ B.gen) := rfl

/-- Canonical evaluation of the literal branch field at the actual residue image. -/
def minpolyScalarBranchLift (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val →ₐ[M] V :=
  liftAlgHom _ (Algebra.ofId M V) (φ B.gen) (minpoly.aeval M (φ B.gen))

theorem minpolyScalarBranchLift_root (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    minpolyScalarBranchLift (M := M) B φ
      (root (minpolyScalarBranch (M := M) B φ).val.val) = φ B.gen :=
  liftAlgHom_root _ _ _ _

/-- The canonical root lift preserves the original upper coefficient map. -/
theorem minpolyScalarBranchLift_algebraMap (B : PowerBasis k A) (φ : A →ₐ[k] V) (a : M) :
    minpolyScalarBranchLift (M := M) B φ
      (algebraMap M (AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val) a) =
      algebraMap M V a :=
  (minpolyScalarBranchLift (M := M) B φ).commutes a

/-- Irreducibility of the original primitive presentation, from the actual power basis. -/
instance powerBasisMinpolyFact (B : PowerBasis k A) : Fact (Irreducible (minpoly k B.gen)) :=
  ⟨minpoly.irreducible B.isIntegral_gen⟩

/-- Evaluation of the scalar branch quotient followed by the original coefficient
quotient map is the original residue embedding after primitive presentation. -/
theorem minpolyScalarBranchLift_comp_adjoinRootMap
    (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    (minpolyScalarBranchLift (M := M) B φ).toRingHom.comp
      (adjoinRootMap (algebraMap k M) (minpoly k B.gen)
        (minpolyScalarBranch (M := M) B φ).val.val (minpolyScalarBranch (M := M) B φ).property) =
      φ.toRingHom.comp (powerBasisMinpolyEquiv B).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change minpolyScalarBranchLift (M := M) B φ
      (adjoinRootMap (algebraMap k M) (minpoly k B.gen)
        (minpolyScalarBranch (M := M) B φ).val.val
        (minpolyScalarBranch (M := M) B φ).property
        (algebraMap k (AdjoinRoot (minpoly k B.gen)) a)) =
      φ (powerBasisMinpolyEquiv B (algebraMap k (AdjoinRoot (minpoly k B.gen)) a))
    rw [adjoinRootMap_algebraMap, minpolyScalarBranchLift_algebraMap,
      AlgEquiv.commutes, φ.commutes, ← IsScalarTower.algebraMap_apply k M V]
  · change minpolyScalarBranchLift (M := M) B φ
      (adjoinRootMap (algebraMap k M) (minpoly k B.gen)
        (minpolyScalarBranch (M := M) B φ).val.val
        (minpolyScalarBranch (M := M) B φ).property (root (minpoly k B.gen))) =
      φ (powerBasisMinpolyEquiv B (root (minpoly k B.gen)))
    rw [adjoinRootMap_root, minpolyScalarBranchLift_root, powerBasisMinpolyEquiv_root]

/-- The branch lift and original scalar quotient map recover the entire original
residue embedding, not merely its value on a generator. -/
theorem minpolyScalarBranchLift_comp_presentation_symm
    (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    ((minpolyScalarBranchLift (M := M) B φ).toRingHom.comp
      (adjoinRootMap (algebraMap k M) (minpoly k B.gen)
        (minpolyScalarBranch (M := M) B φ).val.val
        (minpolyScalarBranch (M := M) B φ).property)).comp
      (powerBasisMinpolyEquiv B).symm.toRingHom = φ.toRingHom := by
  rw [minpolyScalarBranchLift_comp_adjoinRootMap]
  ext a
  exact congrArg φ ((powerBasisMinpolyEquiv B).apply_symm_apply a)

/-- The degree comparison accepts the existing branch-field action, requiring
only that its original quotient root has the specified actual residue image. -/
theorem minpolyScalarBranch_finrank
    (B : PowerBasis k A) (φ : A →ₐ[k] V)
    [Algebra (AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val) V]
    [IsScalarTower M (AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val) V]
    (hroot : algebraMap (AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val) V
      (root (minpolyScalarBranch (M := M) B φ).val.val) = φ B.gen) :
    Module.finrank (IntermediateField.adjoin M {φ B.gen}) V =
      Module.finrank (AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val) V :=
  finrank_adjoin_eq_of_minpoly_eq (φ B.gen) rfl hroot

/-- The canonical branch-field action is exactly its root-evaluation ring map. -/
@[instance_reducible]
def minpolyScalarBranchAlgebra (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    Algebra (AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val) V :=
  (minpolyScalarBranchLift (M := M) B φ).toRingHom.toAlgebra

/-- The canonical action keeps the original upper coefficient field unchanged. -/
theorem minpolyScalarBranchAlgebra_tower (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    let := minpolyScalarBranchAlgebra (M := M) B φ
    IsScalarTower M (AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val) V := by
  let := minpolyScalarBranchAlgebra (M := M) B φ
  exact IsScalarTower.of_algHom (minpolyScalarBranchLift (M := M) B φ)

/-- Relative degree for the canonical original-root evaluation action. -/
theorem minpolyScalarBranch_finrank_canonical (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    let := minpolyScalarBranchAlgebra (M := M) B φ
    Module.finrank (IntermediateField.adjoin M {φ B.gen}) V =
      Module.finrank (AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val) V := by
  let := minpolyScalarBranchAlgebra (M := M) B φ
  let := minpolyScalarBranchAlgebra_tower (M := M) B φ
  exact minpolyScalarBranch_finrank B φ (minpolyScalarBranchLift_root B φ)

end AdjoinRoot
