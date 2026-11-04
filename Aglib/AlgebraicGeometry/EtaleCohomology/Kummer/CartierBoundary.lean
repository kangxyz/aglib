/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphIdeal
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback

/-! The original positive Cartier Kummer class vanishes on the complementary open. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Scheme.Modules.Invertible

universe u w w'

attribute [local instance] hasSheafifyLarge

variable {D U X : Scheme.{u}} (i : D ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} U)]

/-- The inverse of a locally rank-one ideal has zero original Kummer class after
restriction to an open disjoint from the supporting map. -/
theorem picardBoundary_dualIdeal_restrict_zero (h : Disjoint (Set.range i) (Set.range j))
    (hi : IsLocallyRankOne X (Hom.idealModule i)) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    rootsCohomologyPullback j n hn hinv 2
      (picardBoundary X n hn hinv (-classOf X ⟨Hom.idealModule i, hi⟩)) = 0 := by
  let I : LineBundle X := ⟨Hom.idealModule i, hi⟩
  have hI : pullbackClass j (classOf X I) = 0 := by
    rw [← classOf_trivial]
    exact (class_eq_iff U (pullbackLineBundle j I) (trivialLineBundle U)).mpr
      ⟨Hom.idealModulePullbackIsoOfDisjoint i j h ≪≫ (PowerPullback.freeUnitIso U).symm⟩
  change rootsCohomologyPullback j n hn hinv 2
    (picardBoundary X n hn hinv (-classOf X I)) = 0
  rw [picardBoundary_pullback, PullbackTensor.Local.pullbackClass_neg, hI, neg_zero, map_zero]

section Diagonal

variable {S Y V : Scheme.{u}} (p : Y ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (a : V ⟶ pullback p p) [IsOpenImmersion a]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (pullback p p))]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} V)]

/-- The Kummer boundary of the original positive diagonal bundle is zero off the diagonal. -/
theorem diagonalPicardBoundary_restrict_zero
    (h : Disjoint (Set.range (pullback.diagonal p)) (Set.range a))
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(pullback p p, ⊤))) :
    rootsCohomologyPullback a n hn hinv 2
      (picardBoundary (pullback p p) n hn hinv
        (-classOf _ (Hom.diagonalIdealLineBundle Hom.smoothRelativeDivisorIdeal p))) = 0 :=
  picardBoundary_dualIdeal_restrict_zero (pullback.diagonal p) a h
    (Hom.diagonalIdealLineBundle Hom.smoothRelativeDivisorIdeal p).property n hn hinv

end Diagonal

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
