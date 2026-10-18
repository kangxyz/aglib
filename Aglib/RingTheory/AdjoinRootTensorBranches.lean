/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootScalarBranches

/-!
# Actual branch matching after swapping two root-field tensor factors

The branches of `h` over the root field of `p` and the branches of `p` over
the root field of `h` are the same maximal quotients of the two tensor
factors in opposite order. We match every branch and preserve both original
field maps. No equality of polynomial degrees over different base fields,
norm comparison, or normality is assumed.
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

namespace AdjoinRoot

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "hE" => h.map (algebraMap k E)
local notation "pH" => p.map (algebraMap k H)

/-- Swap the original root fields in the whole, unreduced scalar-extension algebra. -/
def tensorSwapEquiv : AdjoinRoot hE ≃ₐ[k] AdjoinRoot pH :=
  ((scalarExtensionEquiv (L := E) h).restrictScalars k).symm.trans
    ((Algebra.TensorProduct.comm k E H).trans
      ((scalarExtensionEquiv (L := H) p).restrictScalars k))

/-- The first original field becomes the scalar-extended old root field. -/
theorem tensorSwapEquiv_algebraMap (a : E) :
    tensorSwapEquiv p h (algebraMap E (AdjoinRoot hE) a) =
      scalarMap (algebraMap k H) p a := by
  have ha : (scalarExtensionEquiv (L := E) h).symm
      (algebraMap E (AdjoinRoot hE) a) = a ⊗ₜ[k] (1 : H) := by
    apply (scalarExtensionEquiv (L := E) h).injective
    rw [AlgEquiv.apply_symm_apply]
    exact ((scalarExtensionEquiv (L := E) h).commutes a).symm
  change scalarExtensionEquiv (L := H) p
    (Algebra.TensorProduct.comm k E H
      ((scalarExtensionEquiv (L := E) h).symm
        (algebraMap E (AdjoinRoot hE) a))) = _
  rw [ha, Algebra.TensorProduct.comm_tmul]
  exact RingHom.congr_fun (scalarExtensionEquiv_comp_includeRight (L := H) p) a

/-- The second original root field becomes the actual coefficient field. -/
theorem tensorSwapEquiv_scalarMap (b : H) :
    tensorSwapEquiv p h (scalarMap (algebraMap k E) h b) =
      algebraMap H (AdjoinRoot pH) b := by
  have hb : (scalarExtensionEquiv (L := E) h).symm
      (scalarMap (algebraMap k E) h b) = (1 : E) ⊗ₜ[k] b := by
    apply (scalarExtensionEquiv (L := E) h).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (RingHom.congr_fun (scalarExtensionEquiv_comp_includeRight (L := E) h) b).symm
  change scalarExtensionEquiv (L := H) p
    (Algebra.TensorProduct.comm k E H
      ((scalarExtensionEquiv (L := E) h).symm
        (scalarMap (algebraMap k E) h b))) = _
  rw [hb, Algebra.TensorProduct.comm_tmul]
  exact (scalarExtensionEquiv (L := H) p).commutes b

/-- The full maximal-spectrum bijection induced by the actual tensor swap. -/
def tensorSwapMaximalEquiv :
    MaximalSpectrum (AdjoinRoot hE) ≃ MaximalSpectrum (AdjoinRoot pH) where
  toFun m := ⟨m.asIdeal.comap (tensorSwapEquiv p h).symm.toRingHom,
    m.isMaximal.comap_bijective _ (tensorSwapEquiv p h).symm.bijective⟩
  invFun m := ⟨m.asIdeal.comap (tensorSwapEquiv p h).toRingHom,
    m.isMaximal.comap_bijective _ (tensorSwapEquiv p h).bijective⟩
  left_inv m := by
    apply MaximalSpectrum.ext
    ext a
    change (tensorSwapEquiv p h).symm (tensorSwapEquiv p h a) ∈ m.asIdeal ↔ a ∈ m.asIdeal
    rw [AlgEquiv.symm_apply_apply]
  right_inv m := by
    apply MaximalSpectrum.ext
    ext a
    change tensorSwapEquiv p h ((tensorSwapEquiv p h).symm a) ∈ m.asIdeal ↔ a ∈ m.asIdeal
    rw [AlgEquiv.apply_symm_apply]

/-- Every irreducible branch is matched, including all nonsplit branches. -/
def tensorSwapBranchEquiv : IrreducibleBranch hE ≃ IrreducibleBranch pH :=
  (branchEquivMaximal hE (Polynomial.map_ne_zero (Fact.out : Irreducible h).ne_zero)).trans
    ((tensorSwapMaximalEquiv p h).trans
      (branchEquivMaximal pH (Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero)).symm)

/-- Matched maximal kernels are related by the original whole-algebra equivalence. -/
theorem tensorSwapBranchEquiv_ideal (q : IrreducibleBranch hE) :
    (branchMaximal pH (tensorSwapBranchEquiv p h q)).asIdeal =
      (branchMaximal hE q).asIdeal.map (tensorSwapEquiv p h).toRingHom := by
  have heq := (branchEquivMaximal pH
    (Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero)).apply_symm_apply
      (tensorSwapMaximalEquiv p h (branchMaximal hE q))
  change branchMaximal pH (tensorSwapBranchEquiv p h q) =
    tensorSwapMaximalEquiv p h (branchMaximal hE q) at heq
  rw [heq]
  exact Ideal.comap_symm (tensorSwapEquiv p h).toRingEquiv

/-- Matched branches have an actual equivalence of their literal quotient fields. -/
def tensorSwapBranchRingEquiv (q : IrreducibleBranch hE) :
    AdjoinRoot q.val.val ≃+* AdjoinRoot (tensorSwapBranchEquiv p h q).val.val :=
  (branchQuotientEquiv hE q).symm.trans
    ((Ideal.quotientEquiv (branchMaximal hE q).asIdeal
      (branchMaximal pH (tensorSwapBranchEquiv p h q)).asIdeal
      (tensorSwapEquiv p h).toRingEquiv (tensorSwapBranchEquiv_ideal p h q)).trans
      (branchQuotientEquiv pH (tensorSwapBranchEquiv p h q)))

/-- The matched quotient maps retain the full tensor-swap square. -/
theorem tensorSwapBranchRingEquiv_divisorMap (q : IrreducibleBranch hE)
    (x : AdjoinRoot hE) :
    tensorSwapBranchRingEquiv p h q (divisorMap hE q.val.val q.property x) =
      divisorMap pH (tensorSwapBranchEquiv p h q).val.val
        (tensorSwapBranchEquiv p h q).property (tensorSwapEquiv p h x) := by
  rw [← branchQuotientEquiv_mk hE q x]
  simp only [tensorSwapBranchRingEquiv, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  exact branchQuotientEquiv_mk _ _ _

/-- The first original field map is the literal residue-field coefficient map on the other side. -/
theorem tensorSwapBranchRingEquiv_algebraMap (q : IrreducibleBranch hE) (a : E) :
    tensorSwapBranchRingEquiv p h q (algebraMap E (AdjoinRoot q.val.val) a) =
      Polynomial.LocalResidue.adjoinRootMap (algebraMap k H) p
        (tensorSwapBranchEquiv p h q).val.val (tensorSwapBranchEquiv p h q).property a := by
  change tensorSwapBranchRingEquiv p h q
    (divisorMap hE q.val.val q.property (algebraMap E (AdjoinRoot hE) a)) = _
  rw [tensorSwapBranchRingEquiv_divisorMap, tensorSwapEquiv_algebraMap]
  exact RingHom.congr_fun (divisorMap_comp_scalarMap (algebraMap k H) p _ _) a

/-- The second original field map becomes the literal coefficient-field inclusion. -/
theorem tensorSwapBranchRingEquiv_adjoinRootMap (q : IrreducibleBranch hE) (b : H) :
    tensorSwapBranchRingEquiv p h q
      (Polynomial.LocalResidue.adjoinRootMap (algebraMap k E) h q.val.val q.property b) =
      algebraMap H (AdjoinRoot (tensorSwapBranchEquiv p h q).val.val) b := by
  rw [← divisorMap_comp_scalarMap, RingHom.comp_apply,
    tensorSwapBranchRingEquiv_divisorMap, tensorSwapEquiv_scalarMap]
  rfl

end AdjoinRoot
