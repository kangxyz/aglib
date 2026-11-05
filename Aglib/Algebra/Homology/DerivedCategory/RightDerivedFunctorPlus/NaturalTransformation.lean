/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.CochainComplexPlus.NaturalTransformation
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition

/-! # Original arbitrary coefficient transformations on right-derived functors

The canonical derived transformation retains the original whole unit square.
No invertibility or scalar linear-category structure is required. Derived
realization universes remain independent.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
namespace CategoryTheory.Functor
universe uA vA wA uB vB wB
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (F : A ⥤ B) [F.Additive] {G : A ⥤ B} [G.Additive]

/-- Derive the actual coefficient transformation using the original units. -/
def rightDerivedFunctorPlusNatTrans (α : F ⟶ G) :
    F.rightDerivedFunctorPlus ⟶ G.rightDerivedFunctorPlus :=
  rightDerivedNatTrans _ _ F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
    (whiskerRight (NatTrans.mapCochainComplexPlus α) DerivedCategory.Plus.Q)

/-- The same original coefficient transformation appears in the derived unit square. -/
theorem rightDerivedFunctorPlusNatTrans_app (α : F ⟶ G) (K : CochainComplex.Plus A) :
    F.rightDerivedFunctorPlusUnit.app K ≫
        (F.rightDerivedFunctorPlusNatTrans α).app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((NatTrans.mapCochainComplexPlus α).app K) ≫
        G.rightDerivedFunctorPlusUnit.app K :=
  rightDerivedNatTrans_app F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
    (whiskerRight (NatTrans.mapCochainComplexPlus α) DerivedCategory.Plus.Q) K

/-- The actual derived transformation preserves the original identity. -/
@[simp]
theorem rightDerivedFunctorPlusNatTrans_id :
    F.rightDerivedFunctorPlusNatTrans (𝟙 F) = 𝟙 F.rightDerivedFunctorPlus := by
  simp only [rightDerivedFunctorPlusNatTrans, NatTrans.mapCochainComplexPlus_id,
    whiskerRight_id', rightDerivedNatTrans_id]

/-- The actual derived transformation preserves the original composition. -/
@[simp]
theorem rightDerivedFunctorPlusNatTrans_comp {H : A ⥤ B} [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) :
    F.rightDerivedFunctorPlusNatTrans (α ≫ β) =
      F.rightDerivedFunctorPlusNatTrans α ≫ G.rightDerivedFunctorPlusNatTrans β := by
  simp only [rightDerivedFunctorPlusNatTrans, NatTrans.mapCochainComplexPlus_comp,
    whiskerRight_comp, rightDerivedNatTrans_comp]

/-- For an isomorphism this is the already installed original comparison map. -/
theorem rightDerivedFunctorPlusNatTrans_iso_hom (e : F ≅ G) :
    F.rightDerivedFunctorPlusNatTrans e.hom = (F.rightDerivedFunctorPlusIso e).hom := rfl

end CategoryTheory.Functor
