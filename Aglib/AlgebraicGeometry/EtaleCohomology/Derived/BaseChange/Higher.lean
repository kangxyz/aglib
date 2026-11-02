/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange.Basic
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.OrdinaryNatTrans

/-!
# The original higher base-change map through ordinary right-derived functors

The component is the native resolution-homology formula and has no
HasDerivedCategory parameter. Naturality uses one proof-local standard family.
The boundary comparison identifies this map with the ORIGINAL derived mate
transport for every selected family and every permitted derived hom-universe.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}

section SelectedModels

variable [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wS'} (AbelianSheaf.{u, u + 1} S')]

variable
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The original higher exchange transport in the actual selected derived categories. -/
def higherBaseChangeMapFromDerived (q : ℕ) :
    higherDirectImage f q ⋙ inverseImage g ⟶ inverseImage g' ⋙ higherDirectImage f' q :=
  (higherBaseChangeSourceIso f g q).hom ≫
    Functor.whiskerLeft
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
      (Functor.whiskerRight (derivedBaseChangeMap f f' g g' h)
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))) ≫
    (higherBaseChangeTargetIso f' g' q).hom

/-- The selected-model boundary retains exactly the original source/mate/target recipe. -/
theorem higherBaseChangeMapFromDerived_eq_transport (q : ℕ) :
    higherBaseChangeMapFromDerived f f' g g' h q =
      (higherBaseChangeSourceIso f g q).hom ≫
        Functor.whiskerLeft
          (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
          (Functor.whiskerRight (derivedBaseChangeMap f f' g g' h)
            (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))) ≫
        (higherBaseChangeTargetIso f' g' q).hom := rfl

private theorem higherBaseChangeTransport_app_eq_ordinary
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    (higherBaseChangeMapFromDerived f f' g g' h q).app F =
      Functor.ordinaryHigherExchangeApp
        (directImage f) (directImage f') (inverseImage g) (inverseImage g')
        (baseChangeMap f f' g g' h) F q :=
  Functor.higherExchangeTransport_app_eq_ordinary
    (directImage f) (directImage f') (inverseImage g) (inverseImage g')
    (baseChangeMap f f' g g' h) (derivedBaseChangeMap f f' g g' h) q
    (higherDirectImageIso f q) (higherDirectImageIso f' q)
    (higherDirectImageIso_eq_native f q) (higherDirectImageIso_eq_native f' q)
    (higherBaseChangeSourceIso f g q).hom (higherBaseChangeTargetIso f' g' q).hom
    (higherBaseChangeMapFromDerived f f' g g' h q)
    (higherBaseChangeMapFromDerived_eq_transport f f' g g' h q)
    (derivedBaseChangeMap_actualUnit f f' g g' h)
    (higherBaseChangeSourceIso_hom_app f g q) (higherBaseChangeTargetIso_hom_app f' g' q) F

end SelectedModels

section Ordinary

variable
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The original higher exchange on intrinsic ordinary right-derived functors. -/
def higherBaseChangeMap (q : ℕ) :
    higherDirectImage f q ⋙ inverseImage g ⟶ inverseImage g' ⋙ higherDirectImage f' q := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X')
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S')
  exact Functor.ordinaryHigherExchangeOfActualUnit
    (directImage f) (directImage f') (inverseImage g) (inverseImage g')
    (baseChangeMap f f' g g' h) (derivedBaseChangeMap f f' g g' h)
    (derivedBaseChangeMap_actualUnit f f' g g' h) q

/-- Naturality of the original higher base change in the coefficient sheaf. -/
@[reassoc]
theorem higherBaseChangeMap_naturality (q : ℕ)
    {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) :
    (inverseImage g).map ((higherDirectImage f q).map a) ≫
        (higherBaseChangeMap f f' g g' h q).app G =
      (higherBaseChangeMap f f' g g' h q).app F ≫
        (higherDirectImage f' q).map ((inverseImage g').map a) :=
  (higherBaseChangeMap f f' g g' h q).naturality a

end Ordinary

section SelectedModels

variable [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wS'} (AbelianSheaf.{u, u + 1} S')]

variable
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- Every original selected-model transport is exactly the intrinsic higher map in every degree. -/
theorem higherBaseChangeMapFromDerived_eq (q : ℕ) :
    higherBaseChangeMapFromDerived f f' g g' h q = higherBaseChangeMap f f' g g' h q := by
  apply NatTrans.ext
  funext F
  exact higherBaseChangeTransport_app_eq_ordinary f f' g g' h F q

/-- The intrinsic higher exchange retains the original transport in any selected derived family. -/
theorem higherBaseChangeMap_eq_transport (q : ℕ) :
    higherBaseChangeMap f f' g g' h q =
      (higherBaseChangeSourceIso f g q).hom ≫
        Functor.whiskerLeft
          (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
          (Functor.whiskerRight (derivedBaseChangeMap f f' g g' h)
            (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))) ≫
        (higherBaseChangeTargetIso f' g' q).hom :=
  (higherBaseChangeMapFromDerived_eq f f' g g' h q).symm

end SelectedModels

end AlgebraicGeometry.Scheme.EtaleCohomology
