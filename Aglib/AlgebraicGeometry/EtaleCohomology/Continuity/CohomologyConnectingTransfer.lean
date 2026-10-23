/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers

/-! # Original connecting maps commute with pullback and coefficient transport -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e
attribute [local instance] hasSheafifyLarge
variable {X Y : Scheme.{u}}
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]

/-- The original cross-site connecting square, followed by a genuine coefficient-sequence map. -/
lemma cohomologyTransfer_connecting (f : Y ⟶ X)
    (T : ShortComplex (AbelianSheaf.{u, u + 1} X))
    (S : ShortComplex (AbelianSheaf.{u, u + 1} Y))
    (hT : T.ShortExact) (hS : S.ShortExact)
    (α : T.map (inverseImage f) ⟶ S) (n : ℕ) :
    AddCommGrpCat.ofHom (Sheaf.H.δ hT n (n + 1) rfl) ≫
        cohomologyTransfer f α.τ₁ (n + 1) =
      cohomologyTransfer f α.τ₃ n ≫
        AddCommGrpCat.ofHom (Sheaf.H.δ hS n (n + 1) rfl) := by
  ext x
  change Sheaf.H.map α.τ₁ (n + 1)
    (cohomologyPullback f T.X₁ (n + 1) (Sheaf.H.δ hT n (n + 1) rfl x)) =
      Sheaf.H.δ hS n (n + 1) rfl
        (Sheaf.H.map α.τ₃ n (cohomologyPullback f T.X₃ n x))
  rw [connecting_cohomologyPullback]
  exact (Sheaf.H.δ_naturality n (n + 1) rfl
    (hT.map_of_exact (inverseImage f)) hS α (cohomologyPullback f T.X₃ n x)).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
