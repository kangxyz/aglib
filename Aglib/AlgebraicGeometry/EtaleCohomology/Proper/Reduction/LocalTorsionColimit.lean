/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.HigherDirectImageColimits
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange
public import Aglib.CategoryTheory.Sites.Torsion.NatTrans
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-! # Original higher exchange on internally torsion coefficients

Both original exchange functors preserve the actual sequential coefficient
colimit for qcqs vertical maps. Naturality and the literal positive factorial-
annihilator cocone reduce its component at a torsion sheaf to its components
at genuinely killed coefficients. No uniform annihilator is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u

attribute [local instance] hasSheafifyLarge


variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']

/-- For qcqs vertical maps, comparison on every genuinely positive killed
coefficient implies invertibility of the defined higher exchange on every
internally torsion coefficient. The higher exchange is intrinsic and requires no derived model. -/
theorem higherBaseChangeMap_isIso_of_torsion_of_killed (q : ℕ)
    (hbounded : ∀ (n : ℕ), n ≠ 0 →
      ∀ F : AbelianSheaf.{u, u + 1} X, n • 𝟙 F = 0 →
        IsIso ((higherBaseChangeMap f f' g g' h q).app F))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    IsIso ((higherBaseChangeMap f f' g g' h q).app F) := by
  let : PreservesColimitsOfShape ℕ (higherDirectImage f q) :=
    Continuity.higherDirectImage_preservesSequentialColimits f q
  let : PreservesColimitsOfShape ℕ (higherDirectImage f' q) :=
    Continuity.higherDirectImage_preservesSequentialColimits f' q
  let L := higherDirectImage f q ⋙ inverseImage g
  let R := inverseImage g' ⋙ higherDirectImage f' q
  let α : L ⟶ R := higherBaseChangeMap f f' g g' h q
  let : PreservesColimitsOfShape ℕ L := inferInstance
  let : PreservesColimitsOfShape ℕ R := inferInstance
  exact Sheaf.natTrans_isIso_of_isTorsion L R α hbounded F hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
