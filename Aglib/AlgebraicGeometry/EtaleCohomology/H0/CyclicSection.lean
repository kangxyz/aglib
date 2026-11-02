/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Mathlib.Data.ZMod.Basic
public import Aglib.CategoryTheory.Sites.SheafCohomology.CyclicSection

/-! # The original constant cyclic coefficient map attached to a torsion section

The native ZMod universal property and original constant/global-section
adjunction define the coefficient map. Its adjoint sends the positive cyclic
generator to the specified original section, with both universe lifts retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) (n : ℕ)
  (r : (globalSections X).obj F) (hr : n • r = 0)

/-- The actual cyclic value homomorphism associated to a torsion section. -/
def cyclicSectionValues : ConstantFinite.value (ULift.{u} (ZMod n)) ⟶
    (globalSections X).obj F :=
  AddCommGrpCat.cyclicSectionValues ((globalSections X).obj F) n r hr
    (AddEquiv.ulift.toAddMonoidHom.comp AddEquiv.ulift.toAddMonoidHom)

/-- The original constant cyclic coefficient map defined by its global section. -/
def cyclicSectionMap : ConstantFinite.coefficient (ULift.{u} (ZMod n)) X ⟶ F :=
  (constantAdjunction X).cyclicSectionMap F n r hr
    (V := ConstantFinite.value (ULift.{u} (ZMod n)))
    (AddEquiv.ulift.toAddMonoidHom.comp AddEquiv.ulift.toAddMonoidHom)

/-- Its native adjoint is exactly the specified value homomorphism. -/
theorem cyclicSectionMap_adjoint :
    ((constantAdjunction X).homEquiv _ _) (cyclicSectionMap F n r hr) =
      cyclicSectionValues F n r hr :=
  ((constantAdjunction X).homEquiv
    (ConstantFinite.value (ULift.{u} (ZMod n))) F).apply_symm_apply
      (cyclicSectionValues F n r hr)

/-- The positive cyclic generator goes to the original chosen section. -/
theorem cyclicSectionValues_one :
    cyclicSectionValues F n r hr (ULift.up (ULift.up (1 : ZMod n))) = r := by
  exact AddCommGrpCat.cyclicSectionValues_one ((globalSections X).obj F) n r hr
    (V := ConstantFinite.value (ULift.{u} (ZMod n)))
    (AddEquiv.ulift.toAddMonoidHom.comp AddEquiv.ulift.toAddMonoidHom)
    (ULift.up (ULift.up (1 : ZMod n))) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
