/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootTowerBranch

/-!
# Changing the upper presentation of an actual root-field tower

An equivalence of the original upper root fields gives an equivalence of the
selected scalar branches over the unchanged lower field. The equivalence
retains the literal upper coefficient maps, and the selected branch has
strictly smaller degree when the lower extension is nontrivial.
-/

@[expose] public noncomputable section

open Polynomial Polynomial.LocalResidue

namespace AdjoinRoot

variable {k : Type*} [Field k] (p h₁ h₂ : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h₁)] [Fact (Irreducible h₂)]

local notation "E" => AdjoinRoot p
local notation "H₁" => AdjoinRoot h₁
local notation "H₂" => AdjoinRoot h₂

/-- The actual relative branch equivalence is the original upper equivalence
conjugated by the two constructed tower-branch identifications. -/
def towerBranchChangeAlgEquiv (e : H₁ ≃ₐ[k] H₂) (f : E →ₐ[k] H₁) :
    AdjoinRoot (towerBranch p h₁ f).val.val ≃ₐ[E]
      AdjoinRoot (towerBranch p h₂ (e.toAlgHom.comp f)).val.val :=
  { (towerBranchRingEquiv p h₁ f).trans
      (e.toRingEquiv.trans (towerBranchRingEquiv p h₂ (e.toAlgHom.comp f)).symm) with
    commutes' := by
      intro a
      change (towerBranchRingEquiv p h₂ (e.toAlgHom.comp f)).symm
        (e (towerBranchRingEquiv p h₁ f (algebraMap E _ a))) = algebraMap E _ a
      apply (towerBranchRingEquiv p h₂ (e.toAlgHom.comp f)).injective
      rw [RingEquiv.apply_symm_apply, towerBranchRingEquiv_algebraMap,
        towerBranchRingEquiv_algebraMap]
      rfl }

/-- The equivalence preserves the prescribed original upper-field map. -/
theorem towerBranchChangeAlgEquiv_adjoinRootMap
    (e : H₁ ≃ₐ[k] H₂) (f : E →ₐ[k] H₁) (a : H₁) :
    towerBranchChangeAlgEquiv p h₁ h₂ e f
      (adjoinRootMap (algebraMap k E) h₁ (towerBranch p h₁ f).val.val
        (towerBranch p h₁ f).property a) =
      adjoinRootMap (algebraMap k E) h₂
        (towerBranch p h₂ (e.toAlgHom.comp f)).val.val
        (towerBranch p h₂ (e.toAlgHom.comp f)).property (e a) := by
  change (towerBranchRingEquiv p h₂ (e.toAlgHom.comp f)).symm
    (e (towerBranchRingEquiv p h₁ f
      (adjoinRootMap (algebraMap k E) h₁ _ _ a))) = _
  rw [towerBranchRingEquiv_adjoinRootMap]
  exact RingHom.congr_fun
    (towerBranchRingEquiv_symm_toRingHom p h₂ (e.toAlgHom.comp f)) (e a)

/-- The quotient compatibility as an equality of the original ring maps. -/
theorem towerBranchChangeAlgEquiv_comp_adjoinRootMap
    (e : H₁ ≃ₐ[k] H₂) (f : E →ₐ[k] H₁) :
    (towerBranchChangeAlgEquiv p h₁ h₂ e f).toRingHom.comp
      (adjoinRootMap (algebraMap k E) h₁ (towerBranch p h₁ f).val.val
        (towerBranch p h₁ f).property) =
      (adjoinRootMap (algebraMap k E) h₂
        (towerBranch p h₂ (e.toAlgHom.comp f)).val.val
        (towerBranch p h₂ (e.toAlgHom.comp f)).property).comp e.toRingHom := by
  apply RingHom.ext
  exact towerBranchChangeAlgEquiv_adjoinRootMap p h₁ h₂ e f

/-- The equivalence also intertwines both actual upper-field identifications. -/
theorem towerBranchRingEquiv_change (e : H₁ ≃ₐ[k] H₂) (f : E →ₐ[k] H₁)
    (a : AdjoinRoot (towerBranch p h₁ f).val.val) :
    towerBranchRingEquiv p h₂ (e.toAlgHom.comp f)
      (towerBranchChangeAlgEquiv p h₁ h₂ e f a) =
        e (towerBranchRingEquiv p h₁ f a) :=
  (towerBranchRingEquiv p h₂ (e.toAlgHom.comp f)).apply_symm_apply _

/-- The two relative presentations have the same actual polynomial degree. -/
theorem towerBranchChange_natDegree (e : H₁ ≃ₐ[k] H₂) (f : E →ₐ[k] H₁) :
    (towerBranch p h₁ f).val.val.natDegree =
      (towerBranch p h₂ (e.toAlgHom.comp f)).val.val.natDegree := by
  have he := (towerBranchChangeAlgEquiv p h₁ h₂ e f).toLinearEquiv.finrank_eq
  simpa only [(AdjoinRoot.powerBasis (towerBranch p h₁ f).val.property.2.ne_zero).finrank,
    (AdjoinRoot.powerBasis
      (towerBranch p h₂ (e.toAlgHom.comp f)).val.property.2.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim] using he

/-- A nontrivial lower root extension makes the actual relative branch degree
strictly smaller than the original upper presentation degree. -/
theorem towerBranch_natDegree_lt (hp : p.Monic) (hh : h₁.Monic)
    (hdeg : 1 < p.natDegree) (f : E →ₐ[k] H₁) :
    (towerBranch p h₁ f).val.val.natDegree < h₁.natDegree := by
  have hq := (towerBranch p h₁ f).val.property.2.natDegree_pos
  calc
    (towerBranch p h₁ f).val.val.natDegree =
        1 * (towerBranch p h₁ f).val.val.natDegree := by simp
    _ < p.natDegree * (towerBranch p h₁ f).val.val.natDegree :=
      Nat.mul_lt_mul_of_pos_right hdeg hq
    _ = h₁.natDegree := towerBranch_natDegree_mul p h₁ hp hh f

end AdjoinRoot
