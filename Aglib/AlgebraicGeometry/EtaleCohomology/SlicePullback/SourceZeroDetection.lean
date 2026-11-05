/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SlicePullback.SourceSquare

/-! # Original represented restriction detected by actual chart pullback

The proved original integer-source square transfers zero in both directions.
The reverse implication uses injectivity of the existing slice comparison,
not a presumed identification of cohomology groups or their maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Sheaf.SliceCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eX eU

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eU} (AbelianSheaf.{u, u + 1} U.left)]

/-- Zero of the original chart pullback forces zero of the original
represented augmentation of the same class. -/
theorem represented_precomp_eq_zero_of_cohomologyPullback_eq_zero
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (x : Sheaf.H.{eX} F q)
    (hx : cohomologyPullback.{u, eX, eU} (X := X) (S := U.left) U.hom F q x = 0) :
    (Ext.mk₀ (representedIntegerAugmentation U)).comp x (Nat.zero_add q) = 0 := by
  let : HasExt.{u + 2}
      (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1}) :=
    HasExt.standard _
  have hzero : cohomologyPullback.{u, eX, eU}
      (X := X) (S := U.left) U.hom F q x =
      cohomologyPullback.{u, eX, eU}
        (X := X) (S := U.left) U.hom F q 0 :=
    hx.trans (map_zero _).symm
  have heq :
      (Ext.mk₀ (representedIntegerAugmentation U)).comp x (Nat.zero_add q) =
      (Ext.mk₀ (representedIntegerAugmentation U)).comp 0 (Nat.zero_add q) := by
    apply (sliceComparison.{eX, u + 2, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) U F q).injective
    rw [← cohomologyPullback_sliceComparison,
      ← cohomologyPullback_sliceComparison, hzero]
  exact heq.trans (Ext.comp_zero _ _ _ _ _)

/-- Actual chart pullback and original represented augmentation have the
same zero condition in every degree and independent Ext universes. -/
theorem cohomologyPullback_eq_zero_iff_represented_precomp_eq_zero
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (x : Sheaf.H.{eX} F q) :
    cohomologyPullback.{u, eX, eU} (X := X) (S := U.left) U.hom F q x = 0 ↔
      (Ext.mk₀ (representedIntegerAugmentation U)).comp x (Nat.zero_add q) = 0 :=
  ⟨represented_precomp_eq_zero_of_cohomologyPullback_eq_zero U F q x,
    cohomologyPullback_eq_zero_of_represented_precomp_eq_zero U F q x⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
