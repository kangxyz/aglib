/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.ResidueMinpolyBranch
public import Lean.Util.CollectAxioms

/-! Actual minimal-polynomial branch maps preserve the full original residue diagram. -/

@[expose] public noncomputable section

open Polynomial AdjoinRoot Polynomial.LocalResidue

namespace AglibTest.ResidueMinpolyBranch

variable {k A M V : Type*} [Field k] [Field A] [Field M] [Field V]
  [Algebra k A] [Algebra k M] [Algebra M V] [Algebra k V]
  [IsScalarTower k M V] [FiniteDimensional M V]

/-- The branch polynomial is the actual minimal polynomial, without associates. -/
theorem actualBranch (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    (minpolyScalarBranch (M := M) B φ).val.val = minpoly M (φ B.gen) := rfl

/-- The named branch really divides the scalar extension of the original polynomial. -/
theorem actualDivisor (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    minpoly M (φ B.gen) ∣ (minpoly k B.gen).map (algebraMap k M) :=
  (minpolyScalarBranch (M := M) B φ).property

/-- Every residue class, not just its generator, has the original image. -/
theorem originalResidueMap (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    ((minpolyScalarBranchLift (M := M) B φ).toRingHom.comp
      (adjoinRootMap (algebraMap k M) (minpoly k B.gen)
        (minpolyScalarBranch (M := M) B φ).val.val
        (minpolyScalarBranch (M := M) B φ).property)).comp
      (powerBasisMinpolyEquiv B).symm.toRingHom = φ.toRingHom :=
  minpolyScalarBranchLift_comp_presentation_symm B φ

/-- The original upper coefficient embedding is unchanged by quotient evaluation. -/
theorem originalCoefficientMap (B : PowerBasis k A) (φ : A →ₐ[k] V) (a : M) :
    minpolyScalarBranchLift (M := M) B φ
      (algebraMap M (AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val) a) =
      algebraMap M V a :=
  minpolyScalarBranchLift_algebraMap B φ a

/-- The degree in the count equals degree for the canonical actual quotient action. -/
theorem originalRelativeDegree (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    let := minpolyScalarBranchAlgebra (M := M) B φ
    Module.finrank (IntermediateField.adjoin M {φ B.gen}) V =
      Module.finrank (AdjoinRoot (minpolyScalarBranch (M := M) B φ).val.val) V :=
  minpolyScalarBranch_finrank_canonical B φ

open Lean in
run_cmd do
  for name in #[``powerBasisMinpolyEquiv, ``powerBasisMinpolyEquiv_root,
      ``minpolyScalarBranch, ``minpolyScalarBranch_val, ``minpolyScalarBranchLift,
      ``minpolyScalarBranchLift_root, ``minpolyScalarBranchLift_algebraMap,
      ``powerBasisMinpolyFact, ``minpolyScalarBranchLift_comp_adjoinRootMap,
      ``minpolyScalarBranchLift_comp_presentation_symm, ``minpolyScalarBranch_finrank,
      ``minpolyScalarBranchAlgebra, ``minpolyScalarBranchAlgebra_tower,
      ``minpolyScalarBranch_finrank_canonical,
      ``actualBranch, ``actualDivisor, ``originalResidueMap, ``originalCoefficientMap,
      ``originalRelativeDegree] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual residue minimal-polynomial branch maps use only standard foundations."

end AglibTest.ResidueMinpolyBranch
