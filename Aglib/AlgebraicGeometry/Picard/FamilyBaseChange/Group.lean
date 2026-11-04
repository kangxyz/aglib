/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FamilyBaseChange
public import Aglib.AlgebraicGeometry.Group.ScalarExtension

/-! The original family comparison is the projection of the group comparison. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Group

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

/-- On the underlying families, the inverse composition comparison of the
original group pullbacks is the canonical family base-change map. -/
theorem groupSchemeBaseChangeComp_inv_left_eq_familyBaseChangeIso_hom
    {S S' : Scheme.{u}} (b : S' ⟶ S) (G : Grp (Over S)) (T : Over S') :
    ((Group.BaseChange.groupSchemeBaseChangeComp T.hom b).inv.app G).hom.hom.left =
      (familyBaseChangeIso G.X.hom b T).hom := by
  apply pullback.hom_ext
  · exact (Group.BaseChange.groupSchemeBaseChangeComp_inv_left_fst T.hom b G).trans
      (familyBaseChangeIso_hom_fst G.X.hom b T).symm
  · exact (Group.BaseChange.groupSchemeBaseChangeComp_inv_left_snd T.hom b G).trans
      (familyBaseChangeIso_hom_snd G.X.hom b T).symm

end AlgebraicGeometry.Scheme.RelativePicard
