/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.AllowedOrders
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AllowedTorsion
public import Mathlib.Algebra.Divisibility.Units

/-! # The exact element-order interpretation of base-invertible torsion

The allowed-annihilator condition is exactly finite additive order invertible
on the entire specified base, not only at the point supporting the stalk.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

/-- In every original geometric stalk, actual element orders are finite and
invertible on the entire base. -/
theorem IsBaseInvertibleTorsion.geometricStalk_addOrderOf {S X : Scheme.{u}}
    {F : AbelianSheaf.{u, u + 1} X} (hF : IsBaseInvertibleTorsion S F)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X)
    (z : ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) :
    IsOfFinAddOrder z ∧ IsUnit (addOrderOf z : Γ(S, ⊤)) := by
  exact (AddGroup.exists_pos_unit_annihilator_iff Γ(S, ⊤) z).mp
    (hF.geometricStalk η z)

/-- The allowed-torsion condition is the literal finite-element-order condition
on original geometric stalks, with invertibility on the whole specified base. -/
theorem isBaseInvertibleTorsion_iff_geometricStalk_orders {S X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) :
    IsBaseInvertibleTorsion S F ↔
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X)
        (z : ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F),
        IsOfFinAddOrder z ∧ IsUnit (addOrderOf z : Γ(S, ⊤)) := by
  constructor
  · intro h Ω _ _ η z
    exact h.geometricStalk_addOrderOf η z
  · intro h
    apply isBaseInvertibleTorsion_of_geometricStalks F
    intro Ω _ _ η z
    exact (AddGroup.exists_pos_unit_annihilator_iff Γ(S, ⊤) z).mpr (h Ω η z)

end AlgebraicGeometry.Scheme.EtaleCohomology
