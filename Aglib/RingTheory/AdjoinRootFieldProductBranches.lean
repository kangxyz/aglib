/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootPiBranches

/-!
# Literal field factors of a polynomial algebra

An actual finite product of fields determines every irreducible polynomial
branch exactly once. The matched field equivalences preserve the original
quotient and coordinate maps, as needed for completed valuation branches.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

/-- A field has exactly its zero maximal ideal. -/
@[instance_reducible]
def fieldMaximalUnique (K : Type*) [Field K] : Unique (MaximalSpectrum K) where
  default := ⟨⊥, inferInstance⟩
  uniq m := MaximalSpectrum.ext ((Ideal.eq_bot_or_top m.asIdeal).resolve_right m.isMaximal.ne_top)

variable {k ι : Type*} [Field k] [Finite ι]
  (D : ι → Type*) [∀ i, Field (D i)]
  (p : k[X]) (hp : p ≠ 0) (ε : AdjoinRoot p ≃+* ∀ i, D i)

/-- The actual field factors biject with the original irreducible branches. -/
def fieldProductBranchEquiv : ι ≃ IrreducibleBranch p := by
  let : ∀ i, Unique (MaximalSpectrum (D i)) := fun i => fieldMaximalUnique (D i)
  exact (Equiv.sigmaUnique ι (fun i => MaximalSpectrum (D i))).symm.trans
    ((maximalPiEquiv D).trans
      ((maximalRingEquiv ε).symm.trans (branchEquivMaximal p hp).symm))

/-- The original coordinate map, before any quotient identification. -/
def fieldProductBranchMap (i : ι) : AdjoinRoot p →+* D i :=
  (Pi.evalRingHom D i).comp ε.toRingHom

/-- The matched branch ideal is literally the coordinate kernel. -/
theorem fieldProductBranchEquiv_ideal (i : ι) :
    (branchMaximal p (fieldProductBranchEquiv D p hp ε i)).asIdeal =
      RingHom.ker (fieldProductBranchMap D p ε i) := by
  have h := (branchEquivMaximal p hp).apply_symm_apply
    ((maximalRingEquiv ε).symm (maximalPiEquiv D ⟨i, (fieldMaximalUnique (D i)).default⟩))
  change branchMaximal p (fieldProductBranchEquiv D p hp ε i) = _ at h
  rw [h]
  rfl

/-- The original quotient field is identified by the actual coordinate map. -/
def fieldProductBranchRingEquiv (i : ι) :
    AdjoinRoot (fieldProductBranchEquiv D p hp ε i).val.val ≃+* D i :=
  (branchQuotientEquiv p (fieldProductBranchEquiv D p hp ε i)).symm.trans
    ((Ideal.quotEquivOfEq (fieldProductBranchEquiv_ideal D p hp ε i)).trans
      ((fieldProductBranchMap D p ε i).quotientKerEquivOfSurjective
        ((Function.surjective_eval _).comp ε.surjective)))

/-- Compatibility holds for every original polynomial-algebra element. -/
theorem fieldProductBranchRingEquiv_divisorMap (i : ι) (x : AdjoinRoot p) :
    fieldProductBranchRingEquiv D p hp ε i
      (divisorMap p (fieldProductBranchEquiv D p hp ε i).val.val
        (fieldProductBranchEquiv D p hp ε i).property x) = ε x i := by
  rw [← branchQuotientEquiv_mk p (fieldProductBranchEquiv D p hp ε i) x]
  simp only [fieldProductBranchRingEquiv, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  rfl

variable [∀ i, Algebra k (D i)]

/-- Base-preserving product maps induce base-preserving branch identifications. -/
def fieldProductBranchAlgEquiv (e : AdjoinRoot p ≃ₐ[k] ∀ i, D i) (i : ι) :
    AdjoinRoot (fieldProductBranchEquiv D p hp e.toRingEquiv i).val.val ≃ₐ[k] D i where
  __ := fieldProductBranchRingEquiv D p hp e.toRingEquiv i
  commutes' a := by
    change fieldProductBranchRingEquiv D p hp e.toRingEquiv i
      (divisorMap p (fieldProductBranchEquiv D p hp e.toRingEquiv i).val.val
        (fieldProductBranchEquiv D p hp e.toRingEquiv i).property
          (algebraMap k (AdjoinRoot p) a)) = _
    rw [fieldProductBranchRingEquiv_divisorMap]
    exact congrFun (e.commutes a) i

end AdjoinRoot
