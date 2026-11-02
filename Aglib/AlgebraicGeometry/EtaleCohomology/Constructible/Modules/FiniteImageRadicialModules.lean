/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageRadicialComparison

/-! # Original module image adjunction for finite radicial morphisms

The native mate equation transfers the original abelian counit to the original
module counit. The resulting whole unit and counit are not a substitute for
the separate geometric constructibility descent obligation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]
  {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [UniversallyInjective f]

/-- The original module counit is invertible for any finite radicial map. -/
theorem finiteRadicial_moduleCounit_isIso (F : ModuleSheaf R Y) :
    IsIso ((moduleImageAdjunction R f).counit.app F) := by
  have hc : IsIso ((inverseImageAdjunction f).counit.app ((moduleUnderlying R Y).obj F)) :=
    finiteRadicial_abelianCounit_isIso f _
  have hm := mateEquiv_counit (moduleImageAdjunction R f) (inverseImageAdjunction f)
    (moduleUnderlyingImageSquare R f) F
  rw [moduleUnderlyingImageSquare_mate] at hm
  change (inverseImage f).map ((moduleDirectImageUnderlyingIso R f).hom.app F) ≫
      (inverseImageAdjunction f).counit.app ((moduleUnderlying R Y).obj F) =
    (moduleInverseImageUnderlyingIso R f).inv.app ((moduleDirectImage R f).obj F) ≫
      (moduleUnderlying R Y).map ((moduleImageAdjunction R f).counit.app F) at hm
  let e := (moduleInverseImageUnderlyingIso R f).symm.app ((moduleDirectImage R f).obj F)
  have hi : IsIso (e.hom ≫
      (moduleUnderlying R Y).map ((moduleImageAdjunction R f).counit.app F)) :=
    hm ▸ inferInstance
  have : IsIso ((moduleUnderlying R Y).map ((moduleImageAdjunction R f).counit.app F)) :=
    (isIso_comp_left_iff e.hom _).mp hi
  exact isIso_of_reflects_iso _ (moduleUnderlying R Y)

/-- The whole original counit, kept before evaluation at a coefficient. -/
def finiteRadicialModuleCounitIso :
    moduleDirectImage R f ⋙ moduleInverseImage R f ≅ 𝟭 _ := by
  have (F : ModuleSheaf R Y) : IsIso ((moduleImageAdjunction R f).counit.app F) :=
    finiteRadicial_moduleCounit_isIso R f F
  have : IsIso (moduleImageAdjunction R f).counit := NatIso.isIso_of_isIso_app _
  exact asIso (moduleImageAdjunction R f).counit

/-- The whole original unit for a finite surjective radicial map. -/
def finiteRadicialModuleUnitIso [Surjective f] :
    𝟭 _ ≅ moduleInverseImage R f ⋙ moduleDirectImage R f := by
  have (F : ModuleSheaf R X) : IsIso ((moduleImageAdjunction R f).unit.app F) :=
    finiteRadicial_moduleUnit_isIso f R F
  have : IsIso (moduleImageAdjunction R f).unit := NatIso.isIso_of_isIso_app _
  exact asIso (moduleImageAdjunction R f).unit

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
