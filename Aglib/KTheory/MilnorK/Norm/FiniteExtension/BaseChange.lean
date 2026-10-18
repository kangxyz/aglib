/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Equiv
public import Aglib.RingTheory.AdjoinRootBranchProduct

/-!
# Actual finite-extension norm base change

Every scalar branch occurs, with its original quotient map. The theorem uses
proved polynomial base change and presentation independence, not a tower law.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue PolynomialNorm AdjoinRoot

variable {k S : Type*} [Field k] [CharZero k] [Field S] [CharZero S]
  [Algebra k S]

/-- The native root field is finite for each monic irreducible presentation. -/
local instance rootFinite (p : MonicIrreducible S) : FiniteDimensional S (AdjoinRoot p.val) :=
  p.property.1.finite_adjoinRoot

/-- Native root presentations compute the actual finite-field norm directly. -/
theorem finiteExtensionNorm_adjoinRoot (p : MonicIrreducible S) (n : ℕ) :
    finiteExtensionNorm S (AdjoinRoot p.val) n = polynomialNorm n p := by
  rw [finiteExtensionNorm_eq_presentation S (AdjoinRoot p.val) n p (AlgEquiv.refl)]
  change (polynomialNorm n p).comp (map n (RingHom.id _)) = _
  rw [map_id, LinearMap.comp_id]

/-- The all-branch form of the proved polynomial coefficient formula. -/
theorem polynomialNorm_restrict_branches (p : MonicIrreducible k)
    [Fintype (IrreducibleBranch (p.val.map (algebraMap k S)))]
    (n : ℕ) (x : K (AdjoinRoot p.val) n) :
    map n (algebraMap k S) (polynomialNorm n p x) =
      ∑ r : IrreducibleBranch (p.val.map (algebraMap k S)),
        finiteExtensionNorm S (AdjoinRoot r.val.val) n
          (map n (adjoinRootMap (algebraMap k S) p.val r.val.val r.property) x) := by
  classical
  rw [polynomialNorm_restrict]
  simp_rw [finiteExtensionNorm_adjoinRoot]
  let f := fun r : IrreducibleBranch (p.val.map (algebraMap k S)) =>
    polynomialNorm n r.val
      (map n (adjoinRootMap (algebraMap k S) p.val r.val.val r.property) x)
  exact Fintype.sum_equiv (placesAboveBranchEquiv (algebraMap k S) p) _ f (fun _ => rfl)

/-- Arbitrary original finite fields satisfy the full scalar-branch formula,
using any actual polynomial presentation and its literal coefficient maps. -/
theorem finiteExtensionNorm_restrict_presentation (E : Type*) [Field E]
    [Algebra k E] [FiniteDimensional k E] (p : MonicIrreducible k)
    (ε : AdjoinRoot p.val ≃ₐ[k] E)
    [Fintype (IrreducibleBranch (p.val.map (algebraMap k S)))]
    (n : ℕ) (x : K E n) :
    map n (algebraMap k S) (finiteExtensionNorm k E n x) =
      ∑ r : IrreducibleBranch (p.val.map (algebraMap k S)),
        finiteExtensionNorm S (AdjoinRoot r.val.val) n
          (map n ((adjoinRootMap (algebraMap k S) p.val r.val.val r.property).comp
            ε.symm.toRingHom) x) := by
  rw [finiteExtensionNorm_eq_presentation k E n p ε, LinearMap.comp_apply,
    polynomialNorm_restrict_branches]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_comp, LinearMap.comp_apply]

end MilnorK
