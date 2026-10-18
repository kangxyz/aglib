/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootTensorBranches
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The actual scalar branch selected by a root-field tower

A specified embedding between two root fields selects the linear factor on
one side of the tensor swap. Its inverse branch has the original upper field
as its literal quotient field, with both original field maps retained.
-/

@[expose] public noncomputable section

open Polynomial Polynomial.LocalResidue

namespace AdjoinRoot

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "hE" => h.map (algebraMap k E)
local notation "pH" => p.map (algebraMap k H)

/-- The literal linear branch selected by the given original field embedding. -/
def towerLinearBranch (f : E →ₐ[k] H) : IrreducibleBranch pH :=
  ⟨⟨X - C (f (root p)), monic_X_sub_C _, irreducible_X_sub_C _⟩, by
    rw [dvd_iff_isRoot, IsRoot, eval_map, ← aeval_def]
    exact AdjoinRoot.aeval_algHom_eq_zero p f⟩

/-- The corresponding branch of the original upper polynomial over the lower root field. -/
def towerBranch (f : E →ₐ[k] H) : IrreducibleBranch hE :=
  (tensorSwapBranchEquiv p h).symm (towerLinearBranch p h f)

/-- Tensor swapping the selected branch gives exactly the prescribed linear polynomial. -/
theorem towerBranch_matched_polynomial (f : E →ₐ[k] H) :
    (tensorSwapBranchEquiv p h (towerBranch p h f)).val.val = X - C (f (root p)) :=
  congrArg (fun q => q.val.val)
    ((tensorSwapBranchEquiv p h).apply_symm_apply (towerLinearBranch p h f))

/-- The matched branch is genuinely linear. -/
theorem towerBranch_matched_natDegree (f : E →ₐ[k] H) :
    (tensorSwapBranchEquiv p h (towerBranch p h f)).val.val.natDegree = 1 := by
  rw [towerBranch_matched_polynomial, natDegree_X_sub_C]

/-- Evaluate the matched linear quotient at the image of the original lower root. -/
def towerBranchTargetEquiv (f : E →ₐ[k] H) :
    AdjoinRoot (tensorSwapBranchEquiv p h (towerBranch p h f)).val.val ≃ₐ[H] H := by
  let g := AdjoinRoot.liftAlgHom
    (tensorSwapBranchEquiv p h (towerBranch p h f)).val.val
    (Algebra.ofId H H) (f (root p)) (by
    rw [towerBranch_matched_polynomial]
    simp)
  exact AlgEquiv.ofBijective g ⟨g.injective, fun a =>
    ⟨algebraMap H _ a, g.commutes a⟩⟩

/-- Evaluation is literal polynomial evaluation at the specified root image. -/
theorem towerBranchTargetEquiv_mk (f : E →ₐ[k] H) (a : H[X]) :
    towerBranchTargetEquiv p h f (AdjoinRoot.mk _ a) = a.eval (f (root p)) := rfl

theorem towerBranchTargetEquiv_root (f : E →ₐ[k] H) :
    towerBranchTargetEquiv p h f
      (root (tensorSwapBranchEquiv p h (towerBranch p h f)).val.val) = f (root p) := by
  rw [← AdjoinRoot.mk_X, towerBranchTargetEquiv_mk, eval_X]

/-- The selected branch field is the original upper root field, by tensor
swapping followed by literal evaluation of the matched linear branch. -/
def towerBranchRingEquiv (f : E →ₐ[k] H) :
    AdjoinRoot (towerBranch p h f).val.val ≃+* H :=
  (tensorSwapBranchRingEquiv p h (towerBranch p h f)).trans
    (towerBranchTargetEquiv p h f).toRingEquiv

/-- The linear evaluation of the matched lower quotient map is the specified embedding. -/
theorem towerBranchTargetEquiv_comp_adjoinRootMap (f : E →ₐ[k] H) :
    (towerBranchTargetEquiv p h f).toRingHom.comp
      (adjoinRootMap (algebraMap k H) p
        (tensorSwapBranchEquiv p h (towerBranch p h f)).val.val
        (tensorSwapBranchEquiv p h (towerBranch p h f)).property) = f.toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change towerBranchTargetEquiv p h f
      (adjoinRootMap (algebraMap k H) p _ _ (algebraMap k E a)) = f (algebraMap k E a)
    rw [adjoinRootMap_algebraMap, AlgEquiv.commutes, f.commutes]
    rfl
  · change towerBranchTargetEquiv p h f
      (adjoinRootMap (algebraMap k H) p _ _ (root p)) = f (root p)
    rw [adjoinRootMap_root, towerBranchTargetEquiv_root]

/-- The branch equivalence retains the specified lower-field inclusion. -/
theorem towerBranchRingEquiv_algebraMap (f : E →ₐ[k] H) (a : E) :
    towerBranchRingEquiv p h f
      (algebraMap E (AdjoinRoot (towerBranch p h f).val.val) a) = f a := by
  change towerBranchTargetEquiv p h f
    (tensorSwapBranchRingEquiv p h (towerBranch p h f) (algebraMap E _ a)) = _
  rw [tensorSwapBranchRingEquiv_algebraMap]
  exact RingHom.congr_fun (towerBranchTargetEquiv_comp_adjoinRootMap p h f) a

/-- The original coefficient-extension quotient map is the inverse branch equivalence. -/
theorem towerBranchRingEquiv_adjoinRootMap (f : E →ₐ[k] H) (a : H) :
    towerBranchRingEquiv p h f
      (adjoinRootMap (algebraMap k E) h (towerBranch p h f).val.val
        (towerBranch p h f).property a) = a := by
  change towerBranchTargetEquiv p h f
    (tensorSwapBranchRingEquiv p h (towerBranch p h f)
      (adjoinRootMap (algebraMap k E) h _ _ a)) = _
  rw [tensorSwapBranchRingEquiv_adjoinRootMap, AlgEquiv.commutes]
  rfl

/-- The branch root maps to the original upper root, not an unspecified conjugate. -/
@[simp]
theorem towerBranchRingEquiv_root (f : E →ₐ[k] H) :
    towerBranchRingEquiv p h f (root (towerBranch p h f).val.val) = root h := by
  simpa only [adjoinRootMap_root] using
    towerBranchRingEquiv_adjoinRootMap p h f (root h)

/-- The inverse equivalence is literally the original upper coefficient map. -/
theorem towerBranchRingEquiv_symm_toRingHom (f : E →ₐ[k] H) :
    (towerBranchRingEquiv p h f).symm.toRingHom =
      adjoinRootMap (algebraMap k E) h (towerBranch p h f).val.val
        (towerBranch p h f).property := by
  apply RingHom.ext
  intro a
  apply (towerBranchRingEquiv p h f).injective
  exact (towerBranchRingEquiv p h f).apply_symm_apply a |>.trans
    (towerBranchRingEquiv_adjoinRootMap p h f a).symm

/-- The actual selected branch degree satisfies the original tower degree formula. -/
theorem towerBranch_natDegree_mul (hp : p.Monic) (hh : h.Monic) (f : E →ₐ[k] H) :
    p.natDegree * (towerBranch p h f).val.val.natDegree = h.natDegree := by
  let : Algebra E H := f.toRingHom.toAlgebra
  let : IsScalarTower k E H := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let e : AdjoinRoot (towerBranch p h f).val.val ≃ₐ[E] H :=
    { towerBranchRingEquiv p h f with commutes' := towerBranchRingEquiv_algebraMap p h f }
  have hd := Module.finrank_mul_finrank k E H
  rw [← e.toLinearEquiv.finrank_eq,
    (AdjoinRoot.powerBasis hp.ne_zero).finrank,
    (AdjoinRoot.powerBasis (towerBranch p h f).val.property.2.ne_zero).finrank,
    (AdjoinRoot.powerBasis hh.ne_zero).finrank] at hd
  exact hd

end AdjoinRoot
