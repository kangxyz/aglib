/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructibleSums
public import Aglib.CategoryTheory.Abelian.ObjectProperty.FiniteColimits

/-! # Original finite colimits of constructible module sheaves

Finite sums and original cokernels give closure under genuine finite diagrams.
Only weak cokernel closure is used, not closure under arbitrary ambient
quotients. The original coefficient ring and original colimit are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] ModuleCat.Sheaf.hasSheafify hasSheafifyLarge
  Abelian.hasFiniteBiproducts

variable {R : Type r} [Ring R] {X : Scheme.{u}}

/-- Native finite coproducts preserve the actual constructible module predicate. -/
instance isConstructible_closedUnderFiniteCoproducts :
    ObjectProperty.IsClosedUnderFiniteCoproducts (IsConstructible (R := R) (X := X)) where
  isClosedUnderColimitsOfShape J _ :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
      rintro F ⟨D, hD⟩
      let e := (biproduct.isoCoproduct (fun j => D.obj ⟨j⟩)) ≪≫ Sigma.isoColimit D
      exact (isConstructible_iff_of_iso e).mp
        (isConstructible_biproduct (fun j => D.obj ⟨j⟩) (fun j => hD ⟨j⟩)))

/-- The original colimit of an actual finite diagram of constructible modules
is constructible over the same Noetherian coefficient ring. -/
theorem isConstructible_of_isColimit [IsNoetherianRing R]
    {J : Type (u + 1)} [SmallCategory J] [Finite (Arrow J)]
    (D : J ⥤ ModuleSheaf R X) {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ j, IsConstructible (D.obj j)) : IsConstructible c.pt :=
  ObjectProperty.prop_of_isColimit_of_finiteCoproducts_cokernels
    (IsConstructible (R := R) (X := X)) D hc hD

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
