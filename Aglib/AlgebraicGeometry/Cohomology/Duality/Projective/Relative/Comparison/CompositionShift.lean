/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward.Shift
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.GlobalSectionsComposition
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.Algebra.Homology.CochainComplexPlus.QuasiIsoShift
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Shift
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TransformationShift

/-!
# Native shifts of geometric composition and affine sections

The original derived-unit equations determine shift compatibility for the
actual geometric composition and structural-global-sections comparisons.
These are the unchanged comparisons used by the affine Serre reduction and
chosen-embedding transfer.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The installed pushforward wrapper retains the original right-derived addition. -/
instance derivedPushforwardPlus_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPushforwardPlus f).Additive :=
  inferInstanceAs ((pushforward f).rightDerivedFunctorPlus.Additive)

/-- Actual geometric derived composition preserves the installed integer shifts. -/
instance derivedPushforwardPlusCompIso_commShift {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (derivedPushforwardPlusCompIso f g).hom.CommShift ℤ := by
  let F := pushforward f
  let G := pushforward g
  let α := (pushforward (f ≫ g)).rightDerivedFunctorPlusUnit
  let β := Functor.whiskerRight
      (NatTrans.mapCochainComplexPlus (pushforwardComp f g).inv) DerivedCategory.Plus.Q ≫
    Functor.rightDerivedFunctorPlusCompUnit F G
  let : β.CommShift ℤ := by
    dsimp only [β]
    infer_instance
  exact Functor.commShift_of_rightDerived_factorization DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso X.Modules) α β (derivedPushforwardPlusCompIso f g).hom
    (by
      apply NatTrans.ext
      funext K
      exact derivedPushforwardPlusCompIso_unit f g K)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived-category structure on modules over the coefficient ring. -/
local instance compositionModuleDerived (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

/-- The original structural derived-sections/direct-image comparison preserves native shifts. -/
instance moduleDerivedGlobalSectionsPushforwardCompIso_commShift
    {R : Type u} [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y) (α : R →+* Γ(Y, ⊤)) :
    (moduleDerivedGlobalSectionsPushforwardCompIso f α).hom.CommShift ℤ := by
  let F := moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)
  let P := Scheme.Modules.pushforward f
  let G := moduleGlobalSectionsFunctorOfHom Y α
  let β := Functor.whiskerRight
      (NatTrans.mapCochainComplexPlus (modulePushforwardGlobalSectionsIso f α).inv)
        DerivedCategory.Plus.Q ≫
    Functor.rightDerivedFunctorPlusCompUnit P G
  let : β.CommShift ℤ := by
    dsimp only [β]
    infer_instance
  exact Functor.commShift_of_rightDerived_factorization DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso X.Modules) F.rightDerivedFunctorPlusUnit β
      (moduleDerivedGlobalSectionsPushforwardCompIso f α).hom
    (by
      apply NatTrans.ext
      funext K
      exact moduleDerivedGlobalSectionsPushforwardCompIso_unit f α K)

end AlgebraicGeometry.Scheme.Cohomology
