/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.NormalConstants.Represented
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Mathlib.Algebra.Group.Shrink

/-! # Finite constants extend canonically across a normal integral scheme

For the original generic inclusion `X.fromSpecStalk (genericPoint X)`, the map
from a constant abelian sheaf to the direct image of its generic restriction is
the original inverse-image adjunction unit followed by `inverseImageConstantIso`.
For every finite value in the native sheaf-value universe, this exact map is an
isomorphism. The proof uses the actual finite trivial cover and generic extension
into integral morphisms. It imposes no Noetherian, Nagata, or order hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.NormalConstants

universe u

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) [IsIntegral X]

/-- The original unit to the generic direct image, with the native constant-sheaf
inverse-image comparison. The map is defined for every abelian coefficient. -/
def constantGenericUnit (A : AddCommGrpCat.{u + 1}) :
    (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A ⟶
      (directImage (X.fromSpecStalk (genericPoint X))).obj
        ((constantSheaf (Scheme.smallEtaleTopology (Spec X.functionField))
          AddCommGrpCat.{u + 1}).obj A) :=
  (inverseImageAdjunction (X.fromSpecStalk (genericPoint X))).unit.app _ ≫
    (directImage (X.fromSpecStalk (genericPoint X))).map
      ((inverseImageConstantIso (X.fromSpecStalk (genericPoint X))).app A).hom

variable [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

/-- The actual generic adjunction unit is invertible for every finite constant
abelian coefficient in the native value universe. -/
theorem isIso_genericUnit_constant (A : AddCommGrpCat.{u + 1}) [Finite A] :
    IsIso ((inverseImageAdjunction (X.fromSpecStalk (genericPoint X))).unit.app
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A)) := by
  let := Fintype.ofFinite A
  have : Small.{u} A := Small.mk'
    ((Fintype.equivFin A).trans (Equiv.ulift.{u}).symm)
  let B := Shrink.{u} A
  have : Finite B := Finite.of_equiv A (equivShrink A)
  let e : ConstantFinite.value B ≅ A :=
    AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans (Shrink.addEquiv (α := A)))
  let r := ConstantFinite.representation B X
  have := r.finite
  have := r.etale
  have := r.commutative
  let η := (inverseImageAdjunction (X.fromSpecStalk (genericPoint X))).unit
  have : IsIso (η.app (representedSheaf r.group)) :=
    isIso_representedGenericUnit X r.group
  have : IsIso (η.app (ConstantFinite.coefficient B X)) :=
    (NatTrans.isIso_app_iff_of_iso η r.iso).mp inferInstance
  exact (NatTrans.isIso_app_iff_of_iso η
    ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).mapIso e)).mp
      inferInstance

/-- Finite constants on a normal integral scheme are the direct image of their
original generic constants, through the exact original unit map. -/
theorem isIso_constantGenericUnit (A : AddCommGrpCat.{u + 1}) [Finite A] :
    IsIso (constantGenericUnit X A) := by
  exact IsIso.comp_isIso' (isIso_genericUnit_constant X A)
    (inferInstance : IsIso ((directImage (X.fromSpecStalk (genericPoint X))).map
      ((inverseImageConstantIso (X.fromSpecStalk (genericPoint X))).app A).hom))

/-- The canonical finite-constant extension isomorphism, with the original unit
as its forward map. -/
def constantGenericIso (A : AddCommGrpCat.{u + 1}) [Finite A] :
    (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A ≅
      (directImage (X.fromSpecStalk (genericPoint X))).obj
        ((constantSheaf (Scheme.smallEtaleTopology (Spec X.functionField))
          AddCommGrpCat.{u + 1}).obj A) := by
  have := isIso_constantGenericUnit X A
  exact asIso (constantGenericUnit X A)

@[simp]
theorem constantGenericIso_hom (A : AddCommGrpCat.{u + 1}) [Finite A] :
    (constantGenericIso X A).hom =
      (inverseImageAdjunction (X.fromSpecStalk (genericPoint X))).unit.app _ ≫
        (directImage (X.fromSpecStalk (genericPoint X))).map
          ((inverseImageConstantIso (X.fromSpecStalk (genericPoint X))).app A).hom := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.NormalConstants
