/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Descent
public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition

/-!
# Actual derived direct image of closed descent

A module annihilated by the kernel of a closed immersion is the original
pushforward of its actual ordinary pullback. Exactness of closed
pushforward and the installed derived-composition comparison transport this
descent to actual bounded-below direct images, in every integer single
degree. The comparison retains the original geometric unit. No
quasicoherence, Noetherianity or derived full faithfulness is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

local instance closedDescentStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ S)
    (M : X.Modules) (hM : killedByIdealSheaf i.ker M) (n : ℤ)

/-- Original closed descent, exact-single comparison and geometric derived
composition give the actual direct-image descent isomorphism. -/
def closedImmersionDerivedDescentIso :
    (derivedPushforwardPlus f).obj ((DerivedCategory.Plus.singleFunctor X.Modules n).obj M) ≅
      (derivedPushforwardPlus (i ≫ f)).obj
        ((DerivedCategory.Plus.singleFunctor Z.Modules n).obj ((pullback i).obj M)) :=
  (derivedPushforwardPlus f).mapIso
      (((DerivedCategory.Plus.singleFunctor X.Modules n).mapIso
        (closedImmersionDescentIso i M hM)).symm) ≪≫
    (derivedPushforwardPlus f).mapIso
      (((pushforward i).rightDerivedFunctorPlusSingleIso n).app ((pullback i).obj M)).symm ≪≫
    ((derivedPushforwardPlusCompIso i f).app
      ((DerivedCategory.Plus.singleFunctor Z.Modules n).obj ((pullback i).obj M))).symm

/-- The original geometric adjunction unit is the first factor of the
actual derived descent map; the other factors are the installed native
exact-single and derived-composition comparisons. -/
theorem closedImmersionDerivedDescentIso_hom :
    (closedImmersionDerivedDescentIso i f M hM n).hom =
      (derivedPushforwardPlus f).map
          ((DerivedCategory.Plus.singleFunctor X.Modules n).map
            ((pullbackPushforwardAdjunction i).unit.app M)) ≫
        (derivedPushforwardPlus f).map
          (((pushforward i).rightDerivedFunctorPlusSingleIso n).inv.app ((pullback i).obj M)) ≫
        (derivedPushforwardPlusCompIso i f).inv.app
          ((DerivedCategory.Plus.singleFunctor Z.Modules n).obj ((pullback i).obj M)) := rfl

/-- Undoing the native derived-composition and exact-single factors gives
exactly the direct image of the original ordinary adjunction unit. -/
@[reassoc]
theorem closedImmersionDerivedDescentIso_hom_unit :
    (closedImmersionDerivedDescentIso i f M hM n).hom ≫
        (derivedPushforwardPlusCompIso i f).hom.app
          ((DerivedCategory.Plus.singleFunctor Z.Modules n).obj ((pullback i).obj M)) ≫
        (derivedPushforwardPlus f).map
          (((pushforward i).rightDerivedFunctorPlusSingleIso n).hom.app ((pullback i).obj M)) =
      (derivedPushforwardPlus f).map
        ((DerivedCategory.Plus.singleFunctor X.Modules n).map
          ((pullbackPushforwardAdjunction i).unit.app M)) := by
  rw [closedImmersionDerivedDescentIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  congr 1

end AlgebraicGeometry.Scheme.Modules
