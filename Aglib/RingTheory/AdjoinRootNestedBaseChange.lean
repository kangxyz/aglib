/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootBranchProduct
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# The actual finite algebra diagram for nested scalar branches

The lower scalar algebra decomposes into every literal branch field. Tensor
associativity then identifies direct upper scalar extension with the product
of upper extensions along those branches, retaining the original scalar maps.
No norm or branch-norm compatibility statement is an assumption.
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

namespace AdjoinRoot

variable {k S : Type*} [Field k] [CharZero k] [Field S] [Algebra k S]
  (p : k[X]) (hp : p.Monic) [Fact (Irreducible p)]

local notation "PRoot" => AdjoinRoot p
local notation "pS" => p.map (algebraMap k S)

/-- The lower-field action on a scalar branch is the original quotient map. -/
@[instance_reducible]
def scalarBranchAlgebra (r : IrreducibleBranch pS) : Algebra PRoot (AdjoinRoot r.val.val) :=
  (Polynomial.LocalResidue.adjoinRootMap (algebraMap k S) p r.val.val r.property).toAlgebra

attribute [local instance] scalarBranchAlgebra

omit [CharZero k] in
/-- Every lower scalar branch keeps the original base scalar tower. -/
theorem scalarBranchBaseTower (r : IrreducibleBranch pS) :
    IsScalarTower k PRoot (AdjoinRoot r.val.val) :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (Polynomial.LocalResidue.adjoinRootMap_algebraMap
      (algebraMap k S) p r.val.val r.property a).symm)

/-- All lower scalar branches form the original lower tensor algebra. -/
def scalarBranchProductEquiv :
    PRoot ⊗[k] S ≃ₐ[PRoot] ∀ r : IrreducibleBranch pS, AdjoinRoot r.val.val :=
  { ((Algebra.TensorProduct.comm k PRoot S).trans
      (((scalarExtensionEquiv (L := S) p).restrictScalars k).trans
        ((branchProductEquiv pS (hp.map _)
          (Polynomial.LocalResidue.squarefree_map _ p)).restrictScalars k))).toRingEquiv with
    commutes' := by
      intro a
      funext r
      change branchProductEquiv pS (hp.map _) (Polynomial.LocalResidue.squarefree_map _ p)
        (scalarExtensionEquiv (L := S) p (1 ⊗ₜ[k] a)) r = _
      rw [branchProductEquiv_apply]
      have h := RingHom.congr_fun (scalarExtensionEquiv_comp_includeRight (L := S) p) a
      change scalarExtensionEquiv (L := S) p (1 ⊗ₜ[k] a) = scalarMap (algebraMap k S) p a at h
      rw [h]
      exact RingHom.congr_fun
        (divisorMap_comp_scalarMap (algebraMap k S) p r.val.val r.property) a }

/-- The scalar-field coordinate in each product factor is literally unchanged. -/
theorem scalarBranchProductEquiv_one_tmul (b : S) (r : IrreducibleBranch pS) :
    scalarBranchProductEquiv p hp ((1 : PRoot) ⊗ₜ[k] b) r =
      algebraMap S (AdjoinRoot r.val.val) b := by
  change branchProductEquiv pS (hp.map _) (Polynomial.LocalResidue.squarefree_map _ p)
    (scalarExtensionEquiv (L := S) p (b ⊗ₜ[k] (1 : PRoot))) r = _
  have hb := (scalarExtensionEquiv (L := S) p).commutes b
  change scalarExtensionEquiv (L := S) p (b ⊗ₜ[k] (1 : PRoot)) = _ at hb
  rw [hb, branchProductEquiv_apply]
  change divisorMap pS r.val.val r.property (mk pS (C b)) = _
  rw [divisorMap_mk]
  rfl

/-- Direct upper base change is the product of all nested lower-branch base
changes, by native tensor associativity and the proved actual lower product. -/
def nestedScalarProductEquiv (E : Type*) [Field E] [Algebra PRoot E] [Algebra k E]
    [IsScalarTower k PRoot E] :
    E ⊗[k] S ≃ₐ[E] ∀ r : IrreducibleBranch pS, E ⊗[PRoot] AdjoinRoot r.val.val := by
  classical
  let : Finite (IrreducibleBranch pS) := finite_irreducibleBranch pS (hp.map _)
  let : Fintype (IrreducibleBranch pS) := Fintype.ofFinite _
  exact (Algebra.TensorProduct.cancelBaseChange k PRoot E E S).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E)
      (scalarBranchProductEquiv p hp)).trans
        (Algebra.TensorProduct.piRight PRoot E E fun r : IrreducibleBranch pS =>
          AdjoinRoot r.val.val))

/-- Every nested factor retains the original upper and scalar-field entries. -/
theorem nestedScalarProductEquiv_tmul (E : Type*) [Field E] [Algebra PRoot E]
    [Algebra k E] [IsScalarTower k PRoot E] (a : E) (b : S)
    (r : IrreducibleBranch pS) :
    nestedScalarProductEquiv p hp E (a ⊗ₜ[k] b) r =
      a ⊗ₜ[PRoot] algebraMap S (AdjoinRoot r.val.val) b := by
  classical
  simp only [nestedScalarProductEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul]
  change a ⊗ₜ[PRoot] scalarBranchProductEquiv p hp (1 ⊗ₜ[k] b) r = _
  rw [scalarBranchProductEquiv_one_tmul]

end AdjoinRoot
