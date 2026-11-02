/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Data.ZMod.Basic

/-! # Original cyclic coefficient maps defined by a killed section

The native ZMod universal property constructs the actual value map, composed
with the supplied original map out of the existing coefficient value. The
original additive-section adjunction transposes that map. No new coefficient
realization or positive-order assumption is introduced.
-/

@[expose] public noncomputable section

namespace AddCommGrpCat

universe w

/-- The actual cyclic value homomorphism from the supplied original coefficient value. -/
def cyclicSectionValues (M : AddCommGrpCat.{w}) (n : ℕ) (r : M) (hr : n • r = 0)
    {V : AddCommGrpCat.{w}} (p : V →+ ZMod n) : V ⟶ M :=
  AddCommGrpCat.ofHom
    ((ZMod.lift n ⟨zmultiplesHom _ r, by simpa only [zmultiplesHom_apply,
      natCast_zsmul] using hr⟩).comp p)

/-- The positive generator maps to the chosen section, for every n including zero. -/
theorem cyclicSectionValues_one (M : AddCommGrpCat.{w}) (n : ℕ) (r : M) (hr : n • r = 0)
    {V : AddCommGrpCat.{w}} (p : V →+ ZMod n) (one : V) (hone : p one = 1) :
    cyclicSectionValues M n r hr p one = r := by
  change (ZMod.lift n ⟨zmultiplesHom _ r, by
    simpa only [zmultiplesHom_apply, natCast_zsmul] using hr⟩) (p one) = r
  rw [hone]
  simpa only [Int.cast_one, zmultiplesHom_apply, one_zsmul] using
    (ZMod.lift_coe n
      ⟨zmultiplesHom _ r, by simpa only [zmultiplesHom_apply, natCast_zsmul] using hr⟩ 1)

end AddCommGrpCat

namespace CategoryTheory.Adjunction

universe u v w

variable {C : Type u} [Category.{v} C]
  {K : AddCommGrpCat.{w} ⥤ C} {Γ : C ⥤ AddCommGrpCat.{w}} (adj : K ⊣ Γ)
  (F : C) (n : ℕ) (r : Γ.obj F) (hr : n • r = 0)
  {V : AddCommGrpCat.{w}} (p : V →+ ZMod n)

/-- The original adjunction inverse applied to the actual cyclic value map. -/
def cyclicSectionMap : K.obj V ⟶ F :=
  (adj.homEquiv V F).symm (AddCommGrpCat.cyclicSectionValues (Γ.obj F) n r hr p)

/-- The native adjoint is exactly the original value homomorphism. -/
theorem cyclicSectionMap_adjoint :
    adj.homEquiv V F (adj.cyclicSectionMap F n r hr p) =
      AddCommGrpCat.cyclicSectionValues (Γ.obj F) n r hr p :=
  Equiv.apply_symm_apply _ _

/-- The adjoint of the original coefficient map sends the positive generator to the section. -/
theorem cyclicSectionMap_adjoint_one (one : V) (hone : p one = 1) :
    adj.homEquiv V F (adj.cyclicSectionMap F n r hr p) one = r := by
  rw [cyclicSectionMap_adjoint]
  exact AddCommGrpCat.cyclicSectionValues_one (Γ.obj F) n r hr p one hone

end CategoryTheory.Adjunction
