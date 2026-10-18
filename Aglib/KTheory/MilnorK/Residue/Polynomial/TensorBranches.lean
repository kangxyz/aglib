/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Polynomial.LinearPlace
public import Aglib.RingTheory.AdjoinRootTensorBranches

/-!
# Actual residues on the matched tensor branches

After matching the branches of `h` over the root field of `p` with those of
`p` over the root field of `h`, the corresponding linear-place restriction
recovers each original branch residue through the proved quotient equivalence.
All original coefficient maps and root images remain explicit.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialResidue

open Polynomial Polynomial.LocalResidue AdjoinRoot

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "hE" => h.map (algebraMap k E)

/-- The literal old-root-field coefficient map into the matched branch. -/
def tensorBranchCoefficientMap (q : IrreducibleBranch hE) :
    E →+* AdjoinRoot (tensorSwapBranchEquiv p h q).val.val :=
  adjoinRootMap (algebraMap k H) p (tensorSwapBranchEquiv p h q).val.val
    (tensorSwapBranchEquiv p h q).property

/-- The actual image of the original finite-place root in the matched branch. -/
def tensorBranchPlaceRoot (q : IrreducibleBranch hE) :
    AdjoinRoot (tensorSwapBranchEquiv p h q).val.val :=
  algebraMap H _ (AdjoinRoot.root h)

/-- Tensor swapping sends the old branch root to the original finite-place root. -/
theorem tensorSwapBranchRingEquiv_root (q : IrreducibleBranch hE) :
    tensorSwapBranchRingEquiv p h q (AdjoinRoot.root q.val.val) =
      tensorBranchPlaceRoot p h q := by
  simpa only [tensorBranchPlaceRoot, adjoinRootMap_root] using
    tensorSwapBranchRingEquiv_adjoinRootMap p h q (AdjoinRoot.root h)

/-- The coefficient square on the matched quotient fields is literal. -/
theorem tensorSwapBranchRingEquiv_comp_algebraMap (q : IrreducibleBranch hE) :
    (tensorSwapBranchRingEquiv p h q).toRingHom.comp (algebraMap E (AdjoinRoot q.val.val)) =
      tensorBranchCoefficientMap p h q := by
  apply RingHom.ext
  exact tensorSwapBranchRingEquiv_algebraMap p h q

/-- The matched root gives an actual linear factor of the original branch polynomial. -/
theorem tensorBranchLinear_dvd (q : IrreducibleBranch hE) :
    X - C (tensorBranchPlaceRoot p h q) ∣ q.val.val.map (tensorBranchCoefficientMap p h q) := by
  rw [dvd_iff_isRoot, IsRoot, eval_map,
    ← tensorSwapBranchRingEquiv_root, ← tensorSwapBranchRingEquiv_comp_algebraMap]
  change eval₂ ((tensorSwapBranchRingEquiv p h q).toRingHom.comp
    (algebraMap E (AdjoinRoot q.val.val)))
    ((tensorSwapBranchRingEquiv p h q).toRingHom (AdjoinRoot.root q.val.val)) q.val.val = 0
  rw [← hom_eval₂]
  exact (congrArg (tensorSwapBranchRingEquiv p h q).toRingHom
    (AdjoinRoot.eval₂_root q.val.val)).trans (map_zero _)

local instance (q : IrreducibleBranch hE) :
    Fact (Irreducible (X - C (tensorBranchPlaceRoot p h q))) :=
  ⟨irreducible_X_sub_C _⟩

/-- Evaluation of the actual linear quotient map is the matched branch equivalence. -/
theorem tensorBranchLinear_map (q : IrreducibleBranch hE) :
    (linearRootEquiv (tensorBranchPlaceRoot p h q)).toRingHom.comp
      (adjoinRootMap (tensorBranchCoefficientMap p h q) q.val.val
        (X - C (tensorBranchPlaceRoot p h q)) (tensorBranchLinear_dvd p h q)) =
      (tensorSwapBranchRingEquiv p h q).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change linearRootEquiv (tensorBranchPlaceRoot p h q)
      (adjoinRootMap (tensorBranchCoefficientMap p h q) q.val.val
        (X - C (tensorBranchPlaceRoot p h q)) _ (algebraMap E _ a)) = _
    rw [adjoinRootMap_algebraMap, AlgEquiv.commutes]
    exact (tensorSwapBranchRingEquiv_algebraMap p h q a).symm
  · change linearRootEquiv (tensorBranchPlaceRoot p h q)
      (adjoinRootMap (tensorBranchCoefficientMap p h q) q.val.val
        (X - C (tensorBranchPlaceRoot p h q)) _ (AdjoinRoot.root q.val.val)) = _
    rw [adjoinRootMap_root]
    rw [← AdjoinRoot.mk_X, linearRootEquiv_mk, eval_X]
    exact (tensorSwapBranchRingEquiv_root p h q).symm

/-- Every actual branch residue is exactly the corresponding linear-place residue
under the original coefficient extension and the tensor-swap quotient map. -/
theorem residueAt_tensorBranch_linear (q : IrreducibleBranch hE) [CharZero E]
    (n : ℕ) (x : K (RatFunc E) (n + 1)) :
    map n (tensorSwapBranchRingEquiv p h q).toRingHom (residueAt q.val.val n x) =
      map n (linearRootEquiv (tensorBranchPlaceRoot p h q)).toRingHom
        (residueAt (X - C (tensorBranchPlaceRoot p h q)) n
          (map (n + 1) (fractionMap (tensorBranchCoefficientMap p h q)) x)) := by
  rw [residueAt_restrict _ q.val.val _ (tensorBranchLinear_dvd p h q)]
  change _ = ((map n _).comp (map n _)) _
  rw [← map_comp, tensorBranchLinear_map]

end MilnorK.PolynomialResidue
