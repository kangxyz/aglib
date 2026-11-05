/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.AllowedNatTrans
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AllowedTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.HigherDirectImageColimits
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange

/-! # Original higher exchange on base-invertible torsion coefficients

The original allowed annihilator diagram and qcqs sequential continuity
assemble the canonical exchange. No uniform annihilator is required, and
no order outside the base-invertible multiplicative set is introduced.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge

/-- Bounded exchange at every allowed positive modulus gives original higher
exchange on every coefficient whose stalk orders are invertible on the base. -/
theorem higherBaseChangeMap_isIso_of_baseInvertibleTorsion_of_killed
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : f' ≫ g = g' ≫ f)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (q : ℕ)
    (hbounded : ∀ n : ℕ, 0 < n → IsUnit (n : Γ(S, ⊤)) →
      ∀ F : AbelianSheaf.{u, u + 1} X, n • 𝟙 F = 0 →
        IsIso ((higherBaseChangeMap f f' g g' h q).app F))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsBaseInvertibleTorsion S F) :
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
  exact Sheaf.natTrans_isIso_of_isLocallyAllowedTorsion
    (baseInvertibleOrders S) L R α hbounded F hF

end AlgebraicGeometry.Scheme.EtaleCohomology
