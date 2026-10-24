/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedConstantSections
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-! # Connected finite constant sections at the native value universe

The actual adjunction unit is transported across a value isomorphism, rather
than replacing the constant coefficient by a different cohomology model.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

attribute [local instance] hasSheafifyLarge

/-- Every finite value in the standard coefficient universe has exactly its
original constant sections on a connected scheme. -/
theorem constantUnit_bijective_value_of_connected
    (X : Scheme.{u}) [ConnectedSpace X] (A : AddCommGrpCat.{u + 1}) [Finite A] :
    Function.Bijective ((constantAdjunction X).unit.app A) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let e₀ : A ≃ ULift.{u} (Fin (Fintype.card A)) :=
    (Fintype.equivFin A).trans Equiv.ulift.symm
  let : Small.{u} A := Small.mk' e₀
  let : Finite (Shrink.{u} A) := Finite.of_equiv A (equivShrink A)
  let e : value (Shrink.{u} A) ≅ A :=
    (AddEquiv.ulift.trans (Shrink.addEquiv (α := A))).toAddCommGrpIso
  have hsmall : IsIso ((constantAdjunction X).unit.app (value (Shrink.{u} A))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (constantUnit_bijective_of_connected X (Shrink.{u} A))
  let : IsIso ((constantAdjunction X).unit.app A) :=
    (NatTrans.isIso_app_iff_of_iso (constantAdjunction X).unit e).mp hsmall
  exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
