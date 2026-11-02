/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.AdditiveFunctor
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.HigherDirectImageColimits
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

/-! # Internal torsion in original higher direct images

For a qcqs morphism, the original higher direct-image functors preserve
internal torsion. Apply abstract additive sequential-colimit preservation at
each original geometric stalk, then use the existing stalk detection theorem.
There is no properness, common annihilator or relative-dimension hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- Original higher direct images under a qcqs morphism preserve internal
torsion, allowing independent local annihilators. -/
theorem higherDirectImage_isTorsion
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    IsTorsion S ((higherDirectImage f q).obj F) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let : (higherDirectImage f q).Additive :=
    Functor.additive_of_iso ((directImage f).rightDerivedSingleHomologyIso q).symm
  let : PreservesColimitsOfShape ℕ (higherDirectImage f q) :=
    Continuity.higherDirectImage_preservesSequentialColimits f q
  apply isTorsion_of_geometricStalks
  intro Ω _ _ η
  let T := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let : T.Additive := Functor.additive_of_preserves_binary_products T
  exact hF.isAddTorsion_obj (higherDirectImage f q ⋙ T)

end AlgebraicGeometry.Scheme.EtaleCohomology
