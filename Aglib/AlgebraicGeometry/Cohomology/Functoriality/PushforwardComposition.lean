/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Flasque.DerivedPushforward
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedPushforwardComposition.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 108]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Composition of actual bounded-below derived direct images

For arbitrary scheme morphisms, pushforward of an injective complex has
flasque terms. Its original derived unit is invertible by the bounded-below
flasque theorem, so the actual composite unit derives composition. The
canonical comparison for a geometric composite retains the original
pushforward composition isomorphism and both installed derived units.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- Standard original module-sheaf derived categories. -/
local instance pushforwardCompositionStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
/-- Actual flasque resolutions prove that the original composite derived unit
derives composition. -/
theorem derivedPushforwardComp_isRightDerived :
    (derivedPushforwardPlus f ⋙ derivedPushforwardPlus g).IsRightDerivedFunctor
      (Functor.rightDerivedFunctorPlusCompUnit
        (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward g))
      (CochainComplex.Plus.quasiIso X.Modules) := by
  let F := Scheme.Modules.pushforward f
  let G := Scheme.Modules.pushforward g
  apply (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus
    (F ⋙ G)).isRightDerivedFunctor_of_isIso
  intro J
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]
  change IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj
    ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J)) ≫
    G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J)))
  have : IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj
      ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J))) := by
    apply isIso_derivedPushforwardPlusUnit_of_flasque
    intro n
    change TopCat.Presheaf.IsFlasque
      ((Scheme.Modules.pushforward f).obj (J.obj.X n).obj).presheaf
    infer_instance
  infer_instance
/-- The actual right-derived composite functor has its canonical comparison. -/
def derivedPushforwardFunctorCompIso :
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).rightDerivedFunctorPlus ≅
      derivedPushforwardPlus f ⋙ derivedPushforwardPlus g := by
  let := derivedPushforwardComp_isRightDerived f g
  exact rightDerivedUnique _ _
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).rightDerivedFunctorPlusUnit
    (Functor.rightDerivedFunctorPlusCompUnit
      (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward g))
    (CochainComplex.Plus.quasiIso X.Modules)
/-- The derived composite comparison retains both original units in their original order. -/
theorem derivedPushforwardFunctorCompIso_unit (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.pushforward f ⋙
      Scheme.Modules.pushforward g).rightDerivedFunctorPlusUnit.app K ≫
        (derivedPushforwardFunctorCompIso f g).hom.app (DerivedCategory.Plus.Q.obj K) =
      (Functor.rightDerivedFunctorPlusCompUnit
        (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward g)).app K := by
  let := derivedPushforwardComp_isRightDerived f g
  simpa only [derivedPushforwardFunctorCompIso, rightDerivedUnique, rightDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
    rightDerivedNatTrans_app
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).rightDerivedFunctorPlus
      (derivedPushforwardPlus f ⋙ derivedPushforwardPlus g)
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).rightDerivedFunctorPlusUnit
      (Functor.rightDerivedFunctorPlusCompUnit
        (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward g))
      (CochainComplex.Plus.quasiIso X.Modules) (𝟙 _) K
/-- The actual bounded-below direct image of a geometric composite. -/
def derivedPushforwardPlusCompIso :
    derivedPushforwardPlus (f ≫ g) ≅ derivedPushforwardPlus f ⋙ derivedPushforwardPlus g :=
  (Scheme.Modules.pushforward (f ≫ g)).rightDerivedFunctorPlusIso
      (Scheme.Modules.pushforwardComp f g).symm ≪≫
    derivedPushforwardFunctorCompIso f g
/-- The geometric comparison retains the original pushforward composition and both derived units. -/
theorem derivedPushforwardPlusCompIso_unit (K : CochainComplex.Plus X.Modules) :
    (derivedPushforwardPlusUnit (f ≫ g)).app K ≫
        (derivedPushforwardPlusCompIso f g).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (Scheme.Modules.pushforwardComp f g)).inv.app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit
        (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward g)).app K := by
  have hM := (Scheme.Modules.pushforward (f ≫ g)).rightDerivedFunctorPlusIso_hom_app
    (Scheme.Modules.pushforwardComp f g).symm K
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc]
  erw [hM]
  rw [Category.assoc, derivedPushforwardFunctorCompIso_unit]
  rfl
end AlgebraicGeometry.Scheme.Modules
end
