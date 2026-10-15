/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
/-!
# The original bounded-below derived identity

The identity functor is right derived through its original termwise comparison.
Derived uniqueness gives a canonical comparison with the installed right-derived
identity, with the original unit equation. The abelian category and its Hom
universe are independent.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory
namespace CategoryTheory.Functor
variable (C : Type u) [Category.{v} C] [Abelian C]
/-- The actual termwise identity functor is the identity on bounded-below complexes. -/
def mapCochainComplexPlusIdIso :
    (𝟭 C).mapCochainComplexPlus ≅ 𝟭 (CochainComplex.Plus C) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K L f
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl)
variable [EnoughInjectives C] [HasDerivedCategory C]
/-- The original complex identity comparison, after localization. -/
def rightDerivedIdentityComparison :
    DerivedCategory.Plus.Q ⋙ 𝟭 (DerivedCategory.Plus C) ≅
      (𝟭 C).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (mapCochainComplexPlusIdIso C).symm _
omit [EnoughInjectives C] in
/-- The identity is the actual right-derived identity through the original comparison. -/
theorem identity_isRightDerivedFunctorPlus :
    (𝟭 (DerivedCategory.Plus C)).IsRightDerivedFunctor
      (rightDerivedIdentityComparison C).inv (CochainComplex.Plus.quasiIso C) :=
  isRightDerivedFunctor_of_inverts _ _ (rightDerivedIdentityComparison C)
/-- The canonical comparison between the actual right-derived identity and the identity. -/
def rightDerivedFunctorPlusIdIso :
    (𝟭 C).rightDerivedFunctorPlus ≅ 𝟭 (DerivedCategory.Plus C) := by
  let := identity_isRightDerivedFunctorPlus C
  exact rightDerivedUnique _ _ (𝟭 C).rightDerivedFunctorPlusUnit
    (rightDerivedIdentityComparison C).inv (CochainComplex.Plus.quasiIso C)
/-- The canonical derived identity comparison retains the original installed unit. -/
theorem rightDerivedFunctorPlusIdIso_unit (K : CochainComplex.Plus C) :
    (𝟭 C).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusIdIso C).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((mapCochainComplexPlusIdIso C).hom.app K) := by
  let := identity_isRightDerivedFunctorPlus C
  simp [rightDerivedFunctorPlusIdIso, rightDerivedUnique, rightDerivedNatIso_hom,
    rightDerivedIdentityComparison]
end CategoryTheory.Functor
