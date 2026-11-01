/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageClosed
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ClosedImmersion

/-! # Genuine constructibility across a surjective closed immersion

The actual module adjunction unit is invertible, by the original scalar
comparison with the original abelian unit. Together with closed-image
constructibility this gives descent without a finite-presentation or bounded
nilpotence assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- The original module adjunction unit is invertible along a surjective
closed immersion, retaining the independent coefficient-ring universe. -/
theorem finiteImage_closedUnit_isIso_of_surjective {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (F : ModuleSheaf R X) : IsIso ((moduleImageAdjunction R i).unit.app F) := by
  have : IsIso ((inverseImageAdjunction i).unit.app ((moduleUnderlying R X).obj F)) :=
    closedDirectImage_unit_isIso_of_surjective i _
  have h : IsIso ((moduleUnderlying R X).map ((moduleImageAdjunction R i).unit.app F) ≫
      (directImage i).map ((moduleInverseImageUnderlyingIso R i).hom.app F)) := by
    exact (ModuleCat.Sheaf.pullbackUnderlyingIso_unit R (siteBaseChange i)
      X.smallEtaleTopology Z.smallEtaleTopology F).symm ▸ inferInstance
  have : IsIso ((moduleUnderlying R X).map ((moduleImageAdjunction R i).unit.app F)) :=
    (isIso_comp_right_iff _ ((directImage i).map
      ((moduleInverseImageUnderlyingIso R i).hom.app F))).mp h
  exact isIso_of_reflects_iso ((moduleImageAdjunction R i).unit.app F) (moduleUnderlying R X)

/-- The entire original unit is retained before evaluation at a coefficient. -/
def finiteImageClosedUnitIso {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i] :
    𝟭 (ModuleSheaf R X) ≅ moduleInverseImage R i ⋙ moduleDirectImage R i := by
  have (F : ModuleSheaf R X) : IsIso ((moduleImageAdjunction R i).unit.app F) :=
    finiteImage_closedUnit_isIso_of_surjective R i F
  have : IsIso (moduleImageAdjunction R i).unit := NatIso.isIso_of_isIso_app _
  exact asIso (moduleImageAdjunction R i).unit

/-- Constructibility of genuine module coefficients is equivalent to that of
its actual restriction to any surjective closed subscheme. -/
theorem isConstructible_iff_surjectiveClosedPullback {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (F : ModuleSheaf R X) :
    IsConstructible F ↔ IsConstructible ((moduleInverseImage R i).obj F) := by
  constructor
  · exact isConstructible_pullback i
  · intro h
    exact (isConstructible_iff_of_iso ((finiteImageClosedUnitIso R i).app F)).mpr
      (isConstructible_surjectiveClosedDirectImage i h)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
