/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Countable.Small

/-! # Finite original colimit points of finite abelian groups

The native direct sum and its native relations quotient are finite. The
universal property compares that native colimit with the supplied cocone point;
the conclusion keeps that original point and independent diagram universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AddCommGrpCat

/-- A finite object family of finite abelian values has a finite supplied
colimit point. There is no bound on the number of diagram arrows. -/
theorem finite_of_isColimit {J : Type v} [Category.{w} J] [Finite J]
    (D : J ⥤ AddCommGrpCat.{u}) [∀ j, Finite (D.obj j)]
    {c : Cocone D} (hc : IsColimit c) : Finite c.pt := by
  classical
  let := Fintype.ofFinite J
  have : Finite (DFinsupp (fun j => D.obj j)) :=
    Finite.of_equiv (∀ j, D.obj j) DFinsupp.equivFunOnFintype.symm
  have : Finite (AddCommGrpCat.Colimits.Quot D) :=
    Finite.of_surjective (QuotientAddGroup.mk' (AddCommGrpCat.Colimits.Relations D))
      (QuotientAddGroup.mk'_surjective _)
  have : Small.{u} (AddCommGrpCat.Colimits.Quot D) := inferInstance
  have : Finite (Shrink.{u} (AddCommGrpCat.Colimits.Quot D)) :=
    Finite.of_equiv _ (equivShrink _)
  let e := hc.coconePointUniqueUpToIso (AddCommGrpCat.Colimits.colimitCoconeIsColimit D)
  exact Finite.of_equiv (Shrink.{u} (AddCommGrpCat.Colimits.Quot D))
    (Iso.addCommGroupIsoToAddEquiv e.symm).toEquiv

/-- The native chosen colimit has the same finite original additive value. -/
theorem finite_colimit {J : Type v} [Category.{w} J] [Finite J]
    (D : J ⥤ AddCommGrpCat.{u}) [∀ j, Finite (D.obj j)] :
    Finite (Limits.colimit D : AddCommGrpCat.{u}) :=
  finite_of_isColimit D (colimit.isColimit D)

end AddCommGrpCat
